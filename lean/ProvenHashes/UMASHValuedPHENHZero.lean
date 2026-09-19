import ProvenHashes.UMASHChunkValuation
import ProvenHashes.UMASHPHENHZero

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet

theorem enh_low_zero_chunk_valuation (x y : Chunk) (tag tag' e : Word)
    (hv : ChunkValuation x y 0) :
    uniformProb (fun k : Chunk => (enh k x tag).1 ^^^ (enh k y tag').1 = e) ≤ (1:ℚ≥0)/q := by
  have ho := (chunk_valuation_increments x y 0 hv).2.2
  simp only [pow_zero,Nat.div_one] at ho
  rcases ho with ho | ho
  · exact enh_low_odd_target_probability x y tag tag' e ho
  · rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => (enh k x tag).1 ^^^ (enh k y tag').1 = e)]
    simpa only [enh,BitVec.mul_comm] using
      enh_low_odd_target_probability (x.2,x.1) (y.2,y.1) tag tag' e ho
-- CHECKPOINT

theorem valued_phenh_zero_raw_target_probability (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (hval : ChunkValuation (lastChunk x) (lastChunk y) 0) (u v : ℕ) :
    uniformProb (lowRawTarget seed x y u v) ≤ (1:ℚ≥0)/q^2 := by
  let ip : Fin 17 := ⟨i, by omega⟩
  let ie : Fin 17 := ⟨x.chunks.length-1, by omega⟩
  let s := x.chunks.length-(i+1)
  let P (w : Chunk) : Prop :=
    (ph w (x.chunks.getD i (0,0))).1 ^^^ (ph w (y.chunks.getD i (0,0))).1 = phenhPHMask s u v
  let Q (w : Chunk) : Prop :=
    (enh w (lastChunk x) (blockTag seed x)).1 ^^^
      (enh w (lastChunk y) (blockTag seed y)).1 = BitVec.ofNat 64 (phenhENHMask s u v)
  have hij : ip ≠ ie := by
    intro h
    have hh := congrArg Fin.val h
    change i = x.chunks.length-1 at hh
    omega
  have hf := chunk_valuation_transfer _ _ _ _ 0
    (single_ph_checksum_difference x y hc hs i hi ho) hval
  have hP : uniformProb P ≤ (1:ℚ≥0)/q := by
    simpa only [pow_zero, Nat.cast_one] using
      ph_low_target_chunk_valuation _ _ (phenhPHMask s u v) 0 hf
  have hQ : uniformProb Q ≤ (1:ℚ≥0)/q :=
    enh_low_zero_chunk_valuation _ _ _ _ _ hval
  have hm : uniformProb (lowRawTarget seed x y u v) ≤
      uniformProb (fun K : Fin 17 → Chunk => P (K ip) ∧ Q (K ie)) := by
    apply probability_mono
    intro K hK
    have ht := single_ph_low_targets (keyPairsEquiv.symm K) seed x y hc i hi ho u v hK.1 hK.2
    simpa only [P, Q, ip, ie, s, blockPHDelta, blockENHDelta, xorChunk,
      keyPair_of_pairs K i (by omega), keyPair_of_pairs K (x.chunks.length-1) (by omega)] using ht
  exact (hm.trans (probability_distinct_coordinates_le ip ie hij P Q _ _ hP hQ)).trans_eq
    (by ring)
-- CHECKPOINT

theorem valued_joint_phenh_zero_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (_hy : y.Valid) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (hp : phDiffCount x y = 1)
    (hval : ChunkValuation (lastChunk x) (lastChunk y) 0) :
    uniformProb (jointEvent seed x y) ≤ (852:ℚ≥0)^2/q^2 := by
  have hxl : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  obtain ⟨i,hi,_hne,ho⟩ := phDiffCount_one_index x y hc hp
  let T := maskSet ×ˢ maskSet
  let F (t : ℕ × ℕ) := lowRawTarget seed x y t.1 t.2
  rw [← uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)]
  calc
    _ ≤ uniformProb (fun K : Fin 17 → Chunk => ∃ t ∈ T, F t K) := by
      apply probability_mono
      intro K hK
      have hm := joint_event_raw_masks (keyPairsEquiv.symm K) seed x y hc hs hK
      refine ⟨((rawPrimaryMask (keyPairsEquiv.symm K) seed x y).1.toNat,
        (rawSecondaryMask (keyPairsEquiv.symm K) seed x y).1.toNat), ?_, rfl, rfl⟩
      exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm.1).1, (Finset.mem_product.mp hm.2).1⟩
    _ ≤ ∑ t ∈ T, uniformProb (F t) := probability_union_bound _ _
    _ ≤ ∑ _t ∈ T, (1:ℚ≥0)/q^2 := Finset.sum_le_sum (fun t _ =>
      valued_phenh_zero_raw_target_probability seed x y hxl hc hs i hi ho hval t.1 t.2)
    _ = _ := by
      simp only [Finset.sum_const, T, Finset.card_product, maskSet_card, nsmul_eq_mul]
      norm_num
      ring
-- CHECKPOINT

end ProvenHashes.UMASH
