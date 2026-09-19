import ProvenHashes.UMASHModularProduct

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- Common bits vanish on the XOR mask, for arbitrary bounded input words. -/
theorem common_bits_mem_mask_targets (n U V e : ℕ) (hU : U < 2^n) (he : U ^^^ V = e) :
    U &&& V ∈ maskValueTargets n e 0 := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.and_le_left.trans_lt hU), ?_⟩
  rw [← he]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases U.testBit i <;> cases V.testBit i <;> simp
-- CHECKPOINT

/-- PROOF2 (20), retaining both ordinary product reductions and the
common-bit target. The congruence is modulo q/2, not modulo q. -/
theorem low_xor_half_product_target (δ ε A B e : ℕ)
    (hδ : 2 ∣ δ) (hε : 2 ∣ ε) (heven : 2 ∣ e)
    (he : lowENHXor 64 δ ε A B = e) :
    ((A:ZMod (2^63))+(δ/2:ℕ))*((B:ZMod (2^63))+(ε/2:ℕ)) =
      (e/2:ℕ)+(A*B%q &&& ((A+δ)*(B+ε)%q):ℕ)-
        (δ/2:ℕ)*(ε/2:ℕ) := by
  let d := δ/2
  let f := ε/2
  let L := A*B%q
  let L' := (A+δ)*(B+ε)%q
  let z := L &&& L'
  have hd : δ = 2*d := (Nat.mul_div_cancel' hδ).symm
  have hf : ε = 2*f := (Nat.mul_div_cancel' hε).symm
  have hs : L+L' = 2*(e/2+z) := by
    have hi := xor_int_expand L L'
    change L ^^^ L' = e at he
    rw [he] at hi
    have h2 := Nat.mul_div_cancel' heven
    dsimp only [z]
    omega
  have hp : A*B+(A+δ)*(B+ε) = 2*((A+d)*(B+f)+d*f) := by
    rw [hd,hf]
    ring
  have hL : Nat.ModEq q (A*B) L := (Nat.mod_mod _ _).symm
  have hL' : Nat.ModEq q ((A+δ)*(B+ε)) L' := (Nat.mod_mod _ _).symm
  have hh := hL.add hL'
  rw [hs,hp] at hh
  change Nat.ModEq (2*2^63) (2*((A+d)*(B+f)+d*f)) (2*(e/2+z)) at hh
  have hhalf := Nat.ModEq.mul_left_cancel' (by decide : 2 ≠ 0) hh
  have heq := (ZMod.natCast_eq_natCast_iff _ _ (2^63)).mpr hhalf
  push_cast at heq
  change ((A:ZMod (2^63))+d)*((B:ZMod (2^63))+f) = (e/2:ℕ)+z-(d:ZMod (2^63))*f
  linear_combination heq
-- CHECKPOINT

/-- The dense low-XOR term of PROOF2 (17) for even increments and target. -/
theorem low_xor_dense_probability_even (δ ε e : ℕ)
    (hδ : 2 ∣ δ) (hε : 2 ∣ ε) (heven : 2 ∣ e) :
    uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
      (65:ℚ≥0)*2^(64-(maskBitSet 64 e).card)/q := by
  let E (z : ℕ) (ab : Word × Word) :=
    ((ab.1.toNat:ZMod (2^63))+(δ/2:ℕ))*((ab.2.toNat:ZMod (2^63))+(ε/2:ℕ)) =
      (e/2:ℕ)+z-(δ/2:ℕ)*(ε/2:ℕ)
  have hcover (ab : Word × Word)
      (he : lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) :
      ∃ z ∈ maskValueTargets 64 e 0, E z ab := by
    refine ⟨ab.1.toNat*ab.2.toNat%q &&& ((ab.1.toNat+δ)*(ab.2.toNat+ε)%q), ?_, ?_⟩
    · exact common_bits_mem_mask_targets 64 _ _ e (Nat.mod_lt _ (by norm_num [q])) he
    · exact low_xor_half_product_target δ ε ab.1.toNat ab.2.toNat e hδ hε heven he
  have hcard : ((maskValueTargets 64 e 0).card:ℚ≥0) ≤
      (2:ℚ≥0)^(64-(maskBitSet 64 e).card) := by
    exact_mod_cast mask_value_targets_card_le 64 e 0
  calc
    _ ≤ uniformProb (fun ab => ∃ z ∈ maskValueTargets 64 e 0, E z ab) := probability_mono hcover
    _ ≤ ∑ z ∈ maskValueTargets 64 e 0, uniformProb (E z) := probability_union_bound _ _
    _ ≤ ∑ _z ∈ maskValueTargets 64 e 0, (65:ℚ≥0)/q := by
      apply Finset.sum_le_sum
      intro z _
      exact shifted_halfword_product_probability (δ/2) (ε/2) _
    _ = (maskValueTargets 64 e 0).card*((65:ℚ≥0)/q) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2:ℚ≥0)^(64-(maskBitSet 64 e).card)*((65:ℚ≥0)/q) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring
-- CHECKPOINT

/-- The dense term with exactly the valuation and divisibility data of Lemma 5.2. -/
theorem low_xor_dense_probability (δ ε r e : ℕ)
    (hδ : 0 < δ ∧ δ < q) (hε : 0 < ε ∧ ε < q)
    (hr : r = min (padicValNat 2 δ) (padicValNat 2 ε)) (hr1 : 1 ≤ r) (he : 2^r ∣ e) :
    uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
      (65:ℚ≥0)*2^(64-(maskBitSet 64 e).card)/q := by
  obtain ⟨_,hd,hε',_⟩ := minimum_increment_padic_factor 64 δ ε r hδ hε hr
  have h2 : 2 ∣ 2^r := by simpa only [pow_one] using pow_dvd_pow 2 hr1
  exact low_xor_dense_probability_even δ ε e (h2.trans hd) (h2.trans hε') (h2.trans he)
-- CHECKPOINT

end ProvenHashes.UMASH
