import ProvenHashes.UMASHLift

namespace ProvenHashes.UMASH

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- Integer presentation of the implemented high lane, including both the fold
and the arbitrary common XOR contribution. -/
def enhHighNat (q₀ A B tag M : ℕ) : ℕ :=
  M ^^^ (A*B % q₀) ^^^ ((A*B/q₀ + tag) % q₀)

theorem xor_common_cancel (M L U V : ℕ) :
    (M ^^^ L ^^^ U) ^^^ (M ^^^ L ^^^ V) = U ^^^ V := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

theorem xor_pattern_recover (M L U m t : ℕ)
    (ht : (M ^^^ L ^^^ U) &&& m = t) :
    U &&& m = (L &&& m) ^^^ (M &&& m) ^^^ t := by
  rw [← ht]
  simp only [Nat.and_xor_distrib_right]
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

/-- The actual low equality and high signed pattern imply the triangular
congruence.  The signed increments include arbitrary input wraps. -/
theorem enh_necessary_congruence (q₀ A B A' B' tag tag' M m t : ℕ)
    (R Q d e : ℤ) (hR : R ≠ 0) (hRQ : R*Q = q₀)
    (hA : (A' : ℤ) = A + R*d) (hB : (B' : ℤ) = B + R*e)
    (hlo : A*B % q₀ = A'*B' % q₀)
    (hm : enhHighNat q₀ A B tag M ^^^ enhHighNat q₀ A' B' tag' M = m)
    (ht : enhHighNat q₀ A B tag M &&& m = t) :
    Int.ModEq (q₀ : ℤ)
      (d*B+e*A+R*d*e+2*Q*(((A*B % q₀ &&& m) ^^^ (M &&& m) ^^^ t : ℕ) : ℤ))
      (Q*((m : ℤ)-((tag' : ℤ)-tag))) := by
  let U := (A*B/q₀+tag)%q₀
  let V := (A'*B'/q₀+tag')%q₀
  let z := (A*B%q₀ &&& m) ^^^ (M &&& m) ^^^ t
  have hm' : U ^^^ V = m := by
    simpa only [enhHighNat, ← hlo, xor_common_cancel, U, V] using hm
  have hz : U &&& m = z := xor_pattern_recover M (A*B%q₀) U m t ht
  have huv : (V : ℤ)-U = (m : ℤ)-2*z := by
    have hd := xor_signed_difference U V
    rw [hm', hz] at hd
    omega
  have hcU : Int.ModEq (q₀ : ℤ) ((A*B/q₀ : ℕ)+tag : ℕ) (U : ℤ) := by
    exact Int.natCast_modEq_iff.mpr (Nat.mod_mod _ _).symm
  have hcV : Int.ModEq (q₀ : ℤ) ((A'*B'/q₀ : ℕ)+tag' : ℕ) (V : ℤ) := by
    exact Int.natCast_modEq_iff.mpr (Nat.mod_mod _ _).symm
  have hhigh := hcV.sub hcU
  simp only [Nat.cast_add] at hhigh
  rw [huv] at hhigh
  have hp : (A'*B' : ℕ) - (A*B : ℕ) =
      (q₀ : ℤ)*((A'*B'/q₀ : ℕ)-(A*B/q₀ : ℕ) : ℤ) := by
    have h1 : (A*B : ℕ) = (A*B%q₀ : ℕ)+(q₀ : ℤ)*(A*B/q₀ : ℕ) := by
      exact_mod_cast (Nat.mod_add_div (A*B) q₀).symm
    have h2 : (A'*B' : ℕ) = (A'*B'%q₀ : ℕ)+(q₀ : ℤ)*(A'*B'/q₀ : ℕ) := by
      exact_mod_cast (Nat.mod_add_div (A'*B') q₀).symm
    rw [h1, h2, hlo]
    ring
  have hprod : R*(d*B+e*A+R*d*e) =
      R*(Q*((A'*B'/q₀ : ℕ)-(A*B/q₀ : ℕ) : ℤ)) := by
    rw [← mul_assoc, hRQ, ← hp]
    push_cast
    rw [hA, hB]
    ring
  have hdiff := mul_left_cancel₀ hR hprod
  have hh := (hhigh.mul_left Q).dvd
  apply Int.modEq_iff_dvd.mpr
  convert hh using 1
  dsimp only [z] at hdiff ⊢
  rw [hdiff]
  ring
-- CHECKPOINT

theorem and_mod_word (w a m : ℕ) (hm : m < 2^w) :
    a % 2^w &&& m = a &&& m := by
  have h := Nat.and_mod_two_pow (a := a) (b := m) (n := w)
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (Nat.and_le_right.trans_lt hm)] at h
  exact h.symm
-- CHECKPOINT

/-- A single lifted ENH fibre, with signed increments fixed by the two wraps.
No condition is imposed on the common mask M. -/
theorem enh_signed_fibre_unique (w A A' B₁ B₂ B₁' B₂' tag tag' M m t : ℕ)
    (R Q d e : ℤ) (hR : R ≠ 0) (hRQ : R*Q = (2 : ℤ)^w) (hd : d%2 = 1)
    (hA : (A' : ℤ) = A+R*d)
    (hB₁ : (B₁' : ℤ) = B₁+R*e) (hB₂ : (B₂' : ℤ) = B₂+R*e)
    (h₁ : B₁ < 2^w) (h₂ : B₂ < 2^w) (hm : m < 2^w)
    (hl₁ : A*B₁ % 2^w = A'*B₁' % 2^w)
    (hl₂ : A*B₂ % 2^w = A'*B₂' % 2^w)
    (hm₁ : enhHighNat (2^w) A B₁ tag M ^^^ enhHighNat (2^w) A' B₁' tag' M = m)
    (hm₂ : enhHighNat (2^w) A B₂ tag M ^^^ enhHighNat (2^w) A' B₂' tag' M = m)
    (ht₁ : enhHighNat (2^w) A B₁ tag M &&& m = t)
    (ht₂ : enhHighNat (2^w) A B₂ tag M &&& m = t) : B₁ = B₂ := by
  have hRQ' : R*Q = (2^w : ℕ) := by exact_mod_cast hRQ
  have ha := enh_necessary_congruence (2^w) A B₁ A' B₁' tag tag' M m t
    R Q d e hR hRQ' hA hB₁ hl₁ hm₁ ht₁
  have hb := enh_necessary_congruence (2^w) A B₂ A' B₂' tag tag' M m t
    R Q d e hR hRQ' hA hB₂ hl₂ hm₂ ht₂
  have he := ha.trans hb.symm
  rw [and_mod_word w (A*B₁) m hm, and_mod_word w (A*B₂) m hm] at he
  apply enh_lift_congruence_unique w A m M t d Q (e*A+R*d*e) hd B₁ B₂ h₁ h₂
  convert he using 1 <;> push_cast <;> ring
-- CHECKPOINT

/-- The natural wrapped operands give precisely the fixed signed increments
used in the preceding uniqueness theorem. -/
theorem enh_wrap_fibre_unique (w r A δ ε B₁ B₂ tag tag' M m t : ℕ)
    (hr : r < w) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ / 2^r) % 2 = 1)
    (h₁ : B₁ < 2^w) (h₂ : B₂ < 2^w) (hm : m < 2^w)
    (hwrap : (B₁+ε)/2^w = (B₂+ε)/2^w)
    (hl₁ : A*B₁ % 2^w = ((A+δ)%2^w)*((B₁+ε)%2^w) % 2^w)
    (hl₂ : A*B₂ % 2^w = ((A+δ)%2^w)*((B₂+ε)%2^w) % 2^w)
    (hm₁ : enhHighNat (2^w) A B₁ tag M ^^^
      enhHighNat (2^w) ((A+δ)%2^w) ((B₁+ε)%2^w) tag' M = m)
    (hm₂ : enhHighNat (2^w) A B₂ tag M ^^^
      enhHighNat (2^w) ((A+δ)%2^w) ((B₂+ε)%2^w) tag' M = m)
    (ht₁ : enhHighNat (2^w) A B₁ tag M &&& m = t)
    (ht₂ : enhHighNat (2^w) A B₂ tag M &&& m = t) : B₁ = B₂ := by
  let R : ℤ := (2 : ℤ)^r
  let Q : ℤ := (2 : ℤ)^(w-r)
  let d : ℤ := (δ / 2^r : ℕ) - ((A+δ)/2^w : ℕ)*Q
  let e : ℤ := (ε / 2^r : ℕ) - ((B₁+ε)/2^w : ℕ)*Q
  have hRQ : R*Q = (2 : ℤ)^w := by
    dsimp [R, Q]
    rw [← pow_add, Nat.add_sub_of_le (le_of_lt hr)]
  have hQ : Q % 2 = 0 := by
    apply Int.emod_eq_zero_of_dvd
    exact dvd_pow_self 2 (by omega : w-r ≠ 0)
  have hd : d % 2 = 1 := by
    dsimp only [d]
    rw [Int.sub_emod, Int.mul_emod, hQ]
    simp only [mul_zero, Int.zero_emod, sub_zero, Int.emod_emod]
    exact_mod_cast hodd
  have hinc (b inc : ℕ) (hinc : 2^r ∣ inc) :
      (((b+inc)%2^w : ℕ) : ℤ) =
        b+R*((inc/2^r : ℕ)-((b+inc)/2^w : ℕ)*Q) := by
    have hi : (inc : ℤ) = R*(inc/2^r : ℕ) := by
      dsimp [R]
      exact_mod_cast (Nat.mul_div_cancel' hinc).symm
    have hmod : (((b+inc)%2^w : ℕ) : ℤ) + (2 : ℤ)^w*((b+inc)/2^w : ℕ) = b+inc := by
      exact_mod_cast Nat.mod_add_div (b+inc) (2^w)
    rw [← hRQ, hi] at hmod
    nlinarith [hmod]
  apply enh_signed_fibre_unique w A ((A+δ)%2^w) B₁ B₂
    ((B₁+ε)%2^w) ((B₂+ε)%2^w) tag tag' M m t R Q d e
    (by dsimp [R]; positivity) hRQ hd (hinc A δ hδ) (hinc B₁ ε hε)
    ?_ h₁ h₂ hm hl₁ hl₂ hm₁ hm₂ ht₁ ht₂
  simpa only [e, hwrap] using hinc B₂ ε hε
-- CHECKPOINT

end ProvenHashes.UMASH
