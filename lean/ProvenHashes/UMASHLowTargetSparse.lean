import ProvenHashes.UMASHHighTargetBound
import ProvenHashes.UMASHLowDistribution

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- Appending the top position adds exactly its indicator to the popcount. -/
theorem mask_bit_set_succ_card (n e : ℕ) :
    (maskBitSet (n+1) e).card = (maskBitSet n e).card + (if e.testBit n then 1 else 0) := by
  simp only [maskBitSet, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  rfl
-- CHECKPOINT

/-- Minimum-valuation division of a nonzero bounded increment gives an odd word. -/
theorem dyadic_increment_padic_factor (n d : ℕ) (hd : 0 < d ∧ d < 2^n) :
    padicValNat 2 d < n ∧ 2^(padicValNat 2 d) ∣ d ∧
      (d/2^(padicValNat 2 d))%2 = 1 := by
  let r := padicValNat 2 d
  have hdiv : 2^r ∣ d := pow_padicValNat_dvd
  have hr : r < n := by
    by_contra h
    have hbig : 2^n ∣ d := (pow_dvd_pow 2 (by omega : n ≤ r)).trans hdiv
    have hle := Nat.le_of_dvd hd.1 hbig
    omega
  have ho : (d/2^r)%2 = 1 := by
    have hn : ¬2 ∣ d/2^r := by
      rintro ⟨z, hz⟩
      apply pow_succ_padicValNat_not_dvd (p := 2) hd.1.ne'
      refine ⟨z, ?_⟩
      change d = 2^(r+1)*z
      calc
        d = 2^r*(d/2^r) := (Nat.mul_div_cancel' hdiv).symm
        _ = _ := by rw [hz, pow_succ]; ring
    have hm : (d/2^r)%2 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
    omega
  exact ⟨hr,hdiv,ho⟩
-- CHECKPOINT

/-- The actual minimum valuation chooses one of the two odd divided increments. -/
theorem minimum_increment_padic_factor (n δ ε r : ℕ)
    (hδ : 0 < δ ∧ δ < 2^n) (hε : 0 < ε ∧ ε < 2^n)
    (hr : r = min (padicValNat 2 δ) (padicValNat 2 ε)) :
    r < n ∧ 2^r ∣ δ ∧ 2^r ∣ ε ∧ ((δ/2^r)%2 = 1 ∨ (ε/2^r)%2 = 1) := by
  have hd := dyadic_increment_padic_factor n δ hδ
  have he := dyadic_increment_padic_factor n ε hε
  rcases le_total (padicValNat 2 δ) (padicValNat 2 ε) with h | h
  · rw [min_eq_left h] at hr
    subst r
    exact ⟨hd.1,hd.2.1,(pow_dvd_pow 2 h).trans he.2.1,Or.inl hd.2.2⟩
  · rw [min_eq_right h] at hr
    subst r
    exact ⟨he.1,(pow_dvd_pow 2 h).trans hd.2.1,he.2.1,Or.inr he.2.2⟩
-- CHECKPOINT

/-- Swapping the two operand coordinates also swaps the two increments. -/
theorem low_xor_probability_swap (δ ε e : ℕ) :
    uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) =
      uniformProb (fun ab : Word × Word => lowENHXor 64 ε δ ab.1.toNat ab.2.toNat = e) := by
  rw [← uniformProb_equiv (Equiv.prodComm Word Word)
    (fun ab : Word × Word => lowENHXor 64 ε δ ab.1.toNat ab.2.toNat = e)]
  apply congrArg uniformProb
  funext ab
  simp [lowENHXor, Nat.mul_comm]
-- CHECKPOINT

/-- Equal low product words are precisely the zero additive-difference fibre. -/
theorem low_xor_zero_iff (δ ε A B : ℕ) :
    lowENHXor 64 δ ε A B = 0 ↔
      (δ:ZMod q)*B+(ε:ZMod q)*A+(δ:ZMod q)*ε = 0 := by
  rw [lowENHXor, Nat.xor_eq_zero]
  change Nat.ModEq q (A*B) ((A+δ)*(B+ε)) ↔ _
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  constructor <;> intro h <;> linear_combination -h
-- CHECKPOINT

/-- The zero low-XOR target has its exact probability, before choosing an orientation. -/
theorem low_xor_zero_probability_oriented (r δ ε : ℕ) (hr : r < 64)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (hodd : (δ/2^r)%2 = 1) :
    uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = 0) =
      (2:ℚ≥0)^r/q := by
  have hQ : 0 < q/2^r := Nat.div_pos
    (Nat.pow_le_pow_right (by decide) hr.le) (by positivity)
  have h := low_additive_distribution r δ ε hr hδ hε hodd ⟨0,hQ⟩
  simp only [Nat.mul_zero, Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat] at h
  rw [← h]
  exact congrArg uniformProb (funext fun ab => propext (low_xor_zero_iff δ ε ab.1.toNat ab.2.toNat))
-- CHECKPOINT

/-- The zero case of PROOF2 Lemma 5.2, with equality and the actual minimum valuation. -/
theorem low_xor_zero_probability (δ ε r : ℕ)
    (hδ : 0 < δ ∧ δ < q) (hε : 0 < ε ∧ ε < q)
    (hr : r = min (padicValNat 2 δ) (padicValNat 2 ε)) :
    uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = 0) =
      (2:ℚ≥0)^r/q := by
  obtain ⟨hr64,hd,he,ho⟩ := minimum_increment_padic_factor 64 δ ε r hδ hε hr
  rcases ho with ho | ho
  · exact low_xor_zero_probability_oriented r δ ε hr64 hd he ho
  · rw [low_xor_probability_swap]
    exact low_xor_zero_probability_oriented r ε δ hr64 he hd ho
-- CHECKPOINT

/-- Removing high bits from an AND pattern keeps it a submask. -/
theorem truncated_and_submask_mem (n L e : ℕ) :
    (L &&& e)%2^n ∈ submaskTargets n e := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by positivity)), ?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  cases L.testBit i <;> cases e.testBit i <;> simp
-- CHECKPOINT

/-- Doubling makes the top bit of a sign pattern irrelevant modulo 2^(n+1). -/
theorem zmod_double_half_residue (n t : ℕ) :
    (2:ZMod (2^(n+1)))*(t%2^n:ℕ) = 2*(t:ZMod (2^(n+1))) := by
  have hm : Nat.ModEq (2^n) (t%2^n) t := Nat.mod_mod _ _
  have hh : Nat.ModEq (2^(n+1)) (2*(t%2^n)) (2*t) := by
    simpa only [pow_succ, Nat.mul_comm] using hm.mul_left' 2
  have he := (ZMod.natCast_eq_natCast_iff _ _ (2^(n+1))).mpr hh
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using he
-- CHECKPOINT

/-- Low XOR targets are covered by additive targets indexed only by the
submask below the top bit. -/
theorem low_xor_sparse_cover (δ ε A B e : ℕ)
    (he : lowENHXor 64 δ ε A B = e) :
    ∃ z ∈ submaskTargets 63 e,
      (δ:ZMod q)*B+(ε:ZMod q)*A+(δ:ZMod q)*ε = (e:ZMod q)-2*z := by
  let L := A*B%q
  let L' := (A+δ)*(B+ε)%q
  have he' : L ^^^ L' = e := he
  have hz := truncated_and_submask_mem 63 L e
  refine ⟨(L &&& e)%2^63, hz, ?_⟩
  have hd : (L':ℤ)-L = (e:ℤ)-2*(L &&& e:ℕ) := by
    have hi := xor_signed_difference L L'
    rw [he'] at hi
    omega
  have hh := congrArg (fun z : ℤ => (z:ZMod q)) hd
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat] at hh
  have hl : (L':ZMod q)-(L:ZMod q) =
      (δ:ZMod q)*B+(ε:ZMod q)*A+(δ:ZMod q)*ε := by
    dsimp only [L,L']
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add]
    ring
  rw [hl] at hh
  rw [show (2:ZMod q)*((L &&& e)%2^63:ℕ) = 2*(L &&& e:ℕ) from
    zmod_double_half_residue 63 (L &&& e)]
  exact hh
-- CHECKPOINT

/-- The sparse term of PROOF2 (17), with its factor-of-two top-bit saving. -/
theorem low_xor_sparse_probability_oriented (r δ ε e : ℕ) (hr : r < 64)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (hodd : (δ/2^r)%2 = 1) :
    uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
      (2:ℚ≥0)^r*2^((maskBitSet 64 e).card-(if e.testBit 63 then 1 else 0))/q := by
  let E (z : ℕ) (ab : Word × Word) :=
    (δ:ZMod q)*ab.2.toNat+(ε:ZMod q)*ab.1.toNat+(δ:ZMod q)*ε = (e:ZMod q)-2*z
  have hc : (maskBitSet 63 e).card =
      (maskBitSet 64 e).card-(if e.testBit 63 then 1 else 0) := by
    have h := mask_bit_set_succ_card 63 e
    change (maskBitSet 64 e).card = (maskBitSet 63 e).card + _ at h
    rw [h, Nat.add_sub_cancel]
  have htargets : ((submaskTargets 63 e).card:ℚ≥0) ≤ (2:ℚ≥0)^(maskBitSet 63 e).card := by
    exact_mod_cast submask_targets_card_le 63 e
  calc
    _ ≤ uniformProb (fun ab => ∃ z ∈ submaskTargets 63 e, E z ab) :=
      probability_mono (fun ab he => low_xor_sparse_cover δ ε ab.1.toNat ab.2.toNat e he)
    _ ≤ ∑ z ∈ submaskTargets 63 e, uniformProb (E z) := probability_union_bound _ _
    _ ≤ ∑ _z ∈ submaskTargets 63 e, ((2:ℚ≥0)^r/q) := by
      apply Finset.sum_le_sum
      intro z _
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        low_additive_target_le r δ ε hr hδ hε hodd ((e:ZMod q)-2*z)
    _ = (submaskTargets 63 e).card*((2:ℚ≥0)^r/q) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2:ℚ≥0)^(maskBitSet 63 e).card*((2:ℚ≥0)^r/q) :=
      mul_le_mul_of_nonneg_right htargets (by positivity)
    _ = _ := by rw [hc]; ring
-- CHECKPOINT

/-- The sparse low-XOR target bound with the actual minimum valuation;
it also covers zero and does not need a positive-valuation premise. -/
theorem low_xor_sparse_probability (δ ε r e : ℕ)
    (hδ : 0 < δ ∧ δ < q) (hε : 0 < ε ∧ ε < q)
    (hr : r = min (padicValNat 2 δ) (padicValNat 2 ε)) :
    uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
      (2:ℚ≥0)^r*2^((maskBitSet 64 e).card-(if e.testBit 63 then 1 else 0))/q := by
  obtain ⟨hr64,hd,he,ho⟩ := minimum_increment_padic_factor 64 δ ε r hδ hε hr
  rcases ho with ho | ho
  · exact low_xor_sparse_probability_oriented r δ ε e hr64 hd he ho
  · rw [low_xor_probability_swap]
    exact low_xor_sparse_probability_oriented r ε δ e hr64 he hd ho
-- CHECKPOINT

end ProvenHashes.UMASH
