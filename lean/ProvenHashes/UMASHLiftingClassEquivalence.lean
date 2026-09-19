import ProvenHashes.UMASHLiftingClasses
import ProvenHashes.UMASHAdditiveProductCore

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

theorem lifting_basis_coefficient (m t j : ℕ) (ht : t &&& m = t) :
    ((m:ℤ)-2*(((2^j) &&& m) ^^^ t : ℕ))-((m:ℤ)-2*t) =
      (-2*((m.testBit j).toNat:ℤ)+4*(t.testBit j).toNat)*(2:ℤ)^j := by
  rw [lifting_function_affine m t (2^j) ht, Nat.two_pow_and, Nat.two_pow_and]
  push_cast
  ring
-- CHECKPOINT

theorem signed_basis_presence (r j : ℕ) (hj : j+1 < r) (a b c d : Bool)
    (hc : c = true → a = true) (hd : d = true → b = true)
    (he : Int.ModEq ((2:ℤ)^r)
      ((-2*(a.toNat:ℤ)+4*c.toNat)*(2:ℤ)^j)
      ((-2*(b.toNat:ℤ)+4*d.toNat)*(2:ℤ)^j)) : a = b := by
  have hp : (2:ℤ)^j*2 < (2:ℤ)^r := by
    rw [← pow_succ]
    exact pow_lt_pow_right₀ (by norm_num) hj
  have hpos : 0 < (2:ℤ)^j := by positivity
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num at *
  all_goals
    have hpos : 0 < (2:ℤ)^j := by positivity
    have hrpos : 0 < (2:ℤ)^r := by positivity
    have hzero := int_dvd_eq_zero_of_bounds ((2:ℤ)^r) _ he.dvd (by nlinarith) (by nlinarith)
    nlinarith
-- CHECKPOINT

/-- The converse of PROOF3 Lemma 5.1: the functions recover exactly the label. -/
theorem lifting_label_of_function_eq (r m t m' t' : ℕ) (hr : 2 ≤ r)
    (ht : t &&& m = t) (ht' : t' &&& m' = t')
    (he : ∀ l : ℕ, Int.ModEq ((2:ℤ)^r)
      ((m:ℤ)-2*((l &&& m) ^^^ t : ℕ))
      ((m':ℤ)-2*((l &&& m') ^^^ t' : ℕ))) :
    m%2^(r-1) = m'%2^(r-1) ∧
      Int.ModEq ((2:ℤ)^r) ((m:ℤ)-2*t) ((m':ℤ)-2*t') := by
  have hc := he 0
  simp only [Nat.zero_and, Nat.zero_xor] at hc
  refine ⟨?_,hc⟩
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < r-1
  · simp only [hj, decide_true, Bool.true_and]
    have hs := (he (2^j)).sub hc
    rw [lifting_basis_coefficient m t j ht, lifting_basis_coefficient m' t' j ht'] at hs
    have hsub (a b : ℕ) (hab : a &&& b = a) : a.testBit j = true → b.testBit j = true := by
      have hb := congrArg (fun x : ℕ => x.testBit j) hab
      simp only [Nat.testBit_and] at hb
      cases ha : a.testBit j <;> cases hb' : b.testBit j <;> simp_all
    exact signed_basis_presence r j (by omega) _ _ _ _ (hsub t m ht) (hsub t' m' ht') hs
  · simp [hj]
-- CHECKPOINT

theorem lifting_function_eq_iff_label (r m t m' t' : ℕ) (hr : 2 ≤ r)
    (ht : t &&& m = t) (ht' : t' &&& m' = t') :
    (∀ l : ℕ, Int.ModEq ((2:ℤ)^r)
      ((m:ℤ)-2*((l &&& m) ^^^ t : ℕ))
      ((m':ℤ)-2*((l &&& m') ^^^ t' : ℕ))) ↔
    m%2^(r-1) = m'%2^(r-1) ∧
      Int.ModEq ((2:ℤ)^r) ((m:ℤ)-2*t) ((m':ℤ)-2*t') := by
  constructor
  · exact lifting_label_of_function_eq r m t m' t' hr ht ht'
  · rintro ⟨hm,hc⟩ l
    exact lifting_function_eq_of_label r m t m' t' l hr ht ht' hm hc
-- CHECKPOINT

/-- XOR translation of the input preserves exactly the same function classes. -/
theorem lifting_function_xor_offset_iff (r m t m' t' M : ℕ) (hr : 2 ≤ r)
    (ht : t &&& m = t) (ht' : t' &&& m' = t') :
    (∀ l : ℕ, Int.ModEq ((2:ℤ)^r)
      ((m:ℤ)-2*(((l ^^^ M) &&& m) ^^^ t : ℕ))
      ((m':ℤ)-2*(((l ^^^ M) &&& m') ^^^ t' : ℕ))) ↔
    m%2^(r-1) = m'%2^(r-1) ∧
      Int.ModEq ((2:ℤ)^r) ((m:ℤ)-2*t) ((m':ℤ)-2*t') := by
  rw [← lifting_function_eq_iff_label r m t m' t' hr ht ht']
  constructor
  · intro h l
    simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using h (l ^^^ M)
  · intro h l
    exact h (l ^^^ M)
-- CHECKPOINT

end ProvenHashes.UMASH
