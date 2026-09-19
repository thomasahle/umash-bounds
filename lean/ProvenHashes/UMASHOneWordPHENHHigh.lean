import ProvenHashes.UMASHOneWordHighLiteral
import ProvenHashes.UMASHValuedPHENHAlgebra
import ProvenHashes.UMASHPHENHProbability

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet

theorem enhChanges_one_word (x y : Block) (he : enhChanges x y = 1) :
    ((lastChunk x).1 ≠ (lastChunk y).1 ∧ (lastChunk x).2 = (lastChunk y).2) ∨
    ((lastChunk x).1 = (lastChunk y).1 ∧ (lastChunk x).2 ≠ (lastChunk y).2) := by
  unfold enhChanges at he
  split_ifs at he <;> simp_all
-- CHECKPOINT

theorem one_word_high_raw_target_probability (seed : Word) (x y : Block)
  (hx : x.chunks.length ≤ 16) (hc : sameCount x y)
  (hs : dataChecksum x = dataChecksum y) (he : enhChanges x y = 1)
  (i : ℕ) (hi : i+1 < x.chunks.length)
  (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
    x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) (u v : ℕ) :
  uniformProb (highRawTarget seed x y i u v) ≤
    (127:ℚ≥0)/q^2 := by
  let ip : Fin 17 := ⟨i, by omega⟩
  let ie : Fin 17 := ⟨x.chunks.length-1, by omega⟩
  let s := x.chunks.length-(i+1)
  let e := phenhENHMask s u v
  let P (w : Chunk) : Prop :=
    xorChunk (ph w (x.chunks.getD i (0,0))) (ph w (y.chunks.getD i (0,0))) = (0,phenhPHMask s u v)
  let Q (w : Chunk) : Prop :=
    (enh w (lastChunk x) (blockTag seed x)).1 = (enh w (lastChunk y) (blockTag seed y)).1 ∧
    (enh w (lastChunk x) (blockTag seed x)).2 ^^^
      (enh w (lastChunk y) (blockTag seed y)).2 = BitVec.ofNat 64 e
  have hij : ip ≠ ie := by
    intro h
    have hh := congrArg Fin.val h
    change i = x.chunks.length-1 at hh
    omega
  have hlast := enhChanges_one_word x y he
  have hne : x.chunks.getD i (0,0) ≠ y.chunks.getD i (0,0) := by
    intro hh
    have hd := single_ph_checksum_difference x y hc hs i hi ho
    rw [hh] at hd
    have h1 := congrArg Prod.fst hd
    have h2 := congrArg Prod.snd hd
    simp only [xorChunk,BitVec.xor_self] at h1 h2
    rcases hlast with ⟨hn,_⟩ | ⟨_,hn⟩
    · exact hn (BitVec.xor_eq_zero_iff.mp h1.symm)
    · exact hn (BitVec.xor_eq_zero_iff.mp h2.symm)
  have hP : uniformProb P ≤ (1:ℚ≥0)/q :=
    ph_xor_target_probability _ _ _ hne
  have hQ : uniformProb Q ≤ (127:ℚ≥0)/q :=
    enh_high_one_word_probability _ _ _ _ _ hlast
  have hm : uniformProb (highRawTarget seed x y i u v) ≤
      uniformProb (fun K : Fin 17 → Chunk => P (K ip) ∧ Q (K ie)) := by
    apply probability_mono
    intro K hK
    have ht := single_ph_high_targets (keyPairsEquiv.symm K) seed x y hc i hi ho u v hK.2.2.1 hK.2.2.2
    have hp : blockPHDelta (keyPairsEquiv.symm K) x y i = (0,phenhPHMask s u v) :=
      Prod.ext hK.1 ht.1
    have hqe : (enh (keyPair (keyPairsEquiv.symm K) (x.chunks.length-1)) (lastChunk x) (blockTag seed x)).1 =
        (enh (keyPair (keyPairsEquiv.symm K) (x.chunks.length-1)) (lastChunk y) (blockTag seed y)).1 :=
      BitVec.xor_eq_zero_iff.mp hK.2.1
    constructor
    · simpa only [P, ip, s, blockPHDelta, keyPair_of_pairs K i (by omega)] using hp
    · simpa only [Q, ie, s, e, blockENHDelta, xorChunk,
        keyPair_of_pairs K (x.chunks.length-1) (by omega)] using And.intro hqe ht.2
  calc
    _ ≤ uniformProb (fun K : Fin 17 → Chunk => P (K ip) ∧ Q (K ie)) := hm
    _ ≤ ((1:ℚ≥0)/q)*((127:ℚ≥0)/q) :=
      probability_distinct_coordinates_le ip ie hij P Q _ _ hP hQ
    _ = _ := by
      have hmul (a : ℚ≥0) : ((1:ℚ≥0)/q)*(a/q) = a/q^2 := by ring
      exact hmul 127
-- CHECKPOINT


/-- For valuations at least four, the raw low masks vanish; the 852²
possible high masks each use the independent PH and one-word ENH atoms. -/
theorem joint_one_word_high_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (_hy : y.Valid) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (hp : phDiffCount x y = 1)
    (he : enhChanges x y = 1) (r : ℕ)
    (hval : ChunkValuation (lastChunk x) (lastChunk y) r) (hr4 : 4 ≤ r) :
    uniformProb (jointEvent seed x y) ≤ (92189808:ℚ≥0)/q^2 := by
  have hxl : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  obtain ⟨i,hi,_hne,ho⟩ := phDiffCount_one_index x y hc hp
  let T := maskSet ×ˢ maskSet
  let F (t : ℕ × ℕ) := highRawTarget seed x y i t.1 t.2
  rw [← uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)]
  calc
    _ ≤ uniformProb (fun K : Fin 17 → Chunk => ∃ t ∈ T, F t K) := by
      apply probability_mono
      intro K hK
      have hm := joint_event_raw_masks (keyPairsEquiv.symm K) seed x y hc hs hK
      have hz := valued_ph_joint_low_zero (keyPairsEquiv.symm K) seed x y hc hs i hi ho r hval hr4 hK
      refine ⟨((rawPrimaryMask (keyPairsEquiv.symm K) seed x y).2.toNat,
        (rawSecondaryMask (keyPairsEquiv.symm K) seed x y).2.toNat), ?_, hz.1,hz.2,rfl,rfl⟩
      exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm.1).2,(Finset.mem_product.mp hm.2).2⟩
    _ ≤ ∑ t ∈ T, uniformProb (F t) := probability_union_bound _ _
    _ ≤ ∑ _t ∈ T, (127:ℚ≥0)/q^2 := Finset.sum_le_sum (fun t _ =>
      one_word_high_raw_target_probability seed x y hxl hc hs he i hi ho t.1 t.2)
    _ = _ := by
      simp only [Finset.sum_const,T,Finset.card_product,maskSet_card,nsmul_eq_mul]
      norm_num
      ring
-- CHECKPOINT

end ProvenHashes.UMASH
