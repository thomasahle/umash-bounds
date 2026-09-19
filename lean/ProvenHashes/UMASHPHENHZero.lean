import ProvenHashes.UMASHPHENHProbability
import ProvenHashes.UMASHPHENHSharp

/-! The valuation-zero PH/ENH row uses independent uniform low targets;
the positive-valuation rows use the sharp PROOF2 ledger. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet
attribute [local irreducible] lowENHXor

theorem enh_low_odd_target_probability (x y : Chunk) (tag tag' e : Word)
    (ho : (y.1-x.1).toNat%2 = 1) :
    uniformProb (fun k : Chunk => (enh k x tag).1 ^^^ (enh k y tag').1 = e) ≤ (1:ℚ≥0)/q := by
  let trans : Chunk ≃ Chunk := Equiv.prodCongr (Equiv.addLeft x.1) (Equiv.addLeft x.2)
  let E (ab : Chunk) : Prop := lowENHXor 64 (y.1-x.1).toNat (y.2-x.2).toNat
    ab.1.toNat ab.2.toNat = e.toNat
  calc
    _ ≤ uniformProb (fun k : Chunk => E (trans k)) := by
      apply probability_mono
      intro k hk
      have ht := congrArg BitVec.toNat hk
      rw [enh_low_xor_to_operands] at ht
      exact ht
    _ = uniformProb E := uniformProb_equiv trans E
    _ = _ := by
      simpa only [E, q, wordFintype] using
        lowENHXor_odd_uniform_bitvec 64 _ _ _ ho e.isLt
-- CHECKPOINT

theorem enh_low_zero_valuation_target (x y : Chunk) (tag tag' e : Word)
    (hx : x.1 ≠ y.1) (hy : x.2 ≠ y.2)
    (hr : min (wordValuation x.1 y.1) (wordValuation x.2 y.2) = 0) :
    uniformProb (fun k : Chunk => (enh k x tag).1 ^^^ (enh k y tag').1 = e) ≤ (1:ℚ≥0)/q := by
  have odd (a b : Word) (hab : a ≠ b) (hv : wordValuation a b = 0) :
      (b-a).toNat%2 = 1 := by
    have hn : 0 < (b-a).toNat := by
      apply Nat.pos_of_ne_zero
      intro h
      exact hab (sub_eq_zero.mp (BitVec.eq_of_toNat_eq h)).symm
    have h := (dyadic_increment_padic_factor 64 (b-a).toNat ⟨hn,(b-a).isLt⟩).2.2
    rw [← wordValuation_eq_sub a b hab, hv] at h
    simpa only [pow_zero, Nat.div_one] using h
  rcases le_total (wordValuation x.1 y.1) (wordValuation x.2 y.2) with h | h
  · rw [min_eq_left h] at hr
    exact enh_low_odd_target_probability x y tag tag' e (odd _ _ hx hr)
  · rw [min_eq_right h] at hr
    rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => (enh k x tag).1 ^^^ (enh k y tag').1 = e)]
    simpa only [enh, BitVec.mul_comm] using
      enh_low_odd_target_probability (x.2,x.1) (y.2,y.1) tag tag' e (odd _ _ hy hr)
-- CHECKPOINT

theorem phenh_zero_raw_target_probability (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (he : enhChanges x y = 2)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (hr : enhValuation x y = 0) (u v : ℕ) :
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
  have hf := single_ph_input_facts x y hc hs he i hi ho
  have hP : uniformProb P ≤ (1:ℚ≥0)/q := by
    simpa only [pow_zero, Nat.cast_one] using
      ph_low_xor_target_probability _ _ (phenhPHMask s u v) hf.1 hf.2.1 0
        (hf.2.2.trans hr).symm
  have hlast := enhChanges_two_words x y he
  have hQ : uniformProb Q ≤ (1:ℚ≥0)/q :=
    enh_low_zero_valuation_target _ _ _ _ _ hlast.1 hlast.2 hr
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

theorem joint_phenh_zero_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (_hy : y.Valid) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (hp : phDiffCount x y = 1)
    (he : enhChanges x y = 2) (hr : enhValuation x y = 0) :
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
      phenh_zero_raw_target_probability seed x y hxl hc hs he i hi ho hr t.1 t.2)
    _ = _ := by
      simp only [Finset.sum_const, T, Finset.card_product, maskSet_card, nsmul_eq_mul]
      norm_num
      ring
-- CHECKPOINT

theorem closed_ph_two_word_enh_bound : ClosedPHTwoWordENHBound := by
  intro seed x y hx hy hc hs hp he hr
  rcases hr with hr | hr
  · exact (joint_phenh_zero_bound seed x y hx hy hc hs hp he hr).trans_lt
      (by apply NNRat.coe_lt_coe.mp; norm_num [q])
  · exact (joint_phenh_iid_lt90 seed x y hx hy hc hs hp he (by omega) (by omega)).trans
      (by apply NNRat.coe_lt_coe.mp; norm_num)
-- CHECKPOINT

end ProvenHashes.UMASH
