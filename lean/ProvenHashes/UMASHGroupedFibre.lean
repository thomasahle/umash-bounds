import ProvenHashes.UMASHLiftingClasses

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

/-- PROOF3 Lemma 5.2: equal function labels may replace equal full patterns
in the existing triangular uniqueness argument. -/
theorem enh_signed_class_fibre_unique
    (w r A A' B₁ B₂ B₁' B₂' tag tag' M m₁ t₁ m₂ t₂ : ℕ)
    (Q d e : ℤ) (hr : 2 ≤ r) (hRQ : (2:ℤ)^r*Q = (2:ℤ)^w)
    (hd : d%2 = 1)
    (hA : (A':ℤ) = A+(2:ℤ)^r*d)
    (hB₁ : (B₁':ℤ) = B₁+(2:ℤ)^r*e)
    (hB₂ : (B₂':ℤ) = B₂+(2:ℤ)^r*e)
    (h₁ : B₁ < 2^w) (h₂ : B₂ < 2^w) (hm₁ : m₁ < 2^w)
    (hsub₁ : t₁ &&& m₁ = t₁) (hsub₂ : t₂ &&& m₂ = t₂)
    (hlabelM : m₁ % 2^(r-1) = m₂ % 2^(r-1))
    (hlabelC : Int.ModEq ((2:ℤ)^r) ((m₁:ℤ)-2*t₁) ((m₂:ℤ)-2*t₂))
    (hl₁ : A*B₁ % 2^w = A'*B₁' % 2^w)
    (hl₂ : A*B₂ % 2^w = A'*B₂' % 2^w)
    (hx₁ : enhHighNat (2^w) A B₁ tag M ^^^ enhHighNat (2^w) A' B₁' tag' M = m₁)
    (hx₂ : enhHighNat (2^w) A B₂ tag M ^^^ enhHighNat (2^w) A' B₂' tag' M = m₂)
    (ht₁ : enhHighNat (2^w) A B₁ tag M &&& m₁ = t₁)
    (ht₂ : enhHighNat (2^w) A B₂ tag M &&& m₂ = t₂) : B₁ = B₂ := by
  have hRQ' : (2:ℤ)^r*Q = (2^w:ℕ) := by exact_mod_cast hRQ
  have ha := enh_necessary_congruence (2^w) A B₁ A' B₁' tag tag' M m₁ t₁
    ((2:ℤ)^r) Q d e (by positivity) hRQ' hA hB₁ hl₁ hx₁ ht₁
  have hb := enh_necessary_congruence (2^w) A B₂ A' B₂' tag tag' M m₂ t₂
    ((2:ℤ)^r) Q d e (by positivity) hRQ' hA hB₂ hl₂ hx₂ ht₂
  have hf := lifting_function_eq_of_label r m₁ t₁ m₂ t₂ ((A*B₂%2^w) ^^^ M)
    hr hsub₁ hsub₂ hlabelM hlabelC
  simp only [Nat.and_xor_distrib_right] at hf
  have hfQ : Int.ModEq ((2^w:ℕ):ℤ)
      (Q*((m₁:ℤ)-2*(((A*B₂%2^w &&& m₁) ^^^ (M &&& m₁) ^^^ t₁ : ℕ):ℤ)))
      (Q*((m₂:ℤ)-2*(((A*B₂%2^w &&& m₂) ^^^ (M &&& m₂) ^^^ t₂ : ℕ):ℤ))) := by
    have hh := hf.mul_left' (c := Q)
    simpa only [mul_comm Q ((2:ℤ)^r), hRQ'] using hh
  have he : Int.ModEq ((2^w:ℕ):ℤ)
      (d*B₁+e*A+(2:ℤ)^r*d*e+
        2*Q*(((A*B₁%2^w &&& m₁) ^^^ (M &&& m₁) ^^^ t₁ : ℕ):ℤ))
      (d*B₂+e*A+(2:ℤ)^r*d*e+
        2*Q*(((A*B₂%2^w &&& m₁) ^^^ (M &&& m₁) ^^^ t₁ : ℕ):ℤ)) := by
    apply Int.modEq_iff_dvd.mpr
    convert dvd_add (dvd_sub ha.dvd hb.dvd) hfQ.dvd using 1 <;> ring
  rw [and_mod_word w (A*B₁) m₁ hm₁, and_mod_word w (A*B₂) m₁ hm₁] at he
  apply enh_lift_congruence_unique w A m₁ M t₁ d Q (e*A+(2:ℤ)^r*d*e)
    hd B₁ B₂ h₁ h₂
  convert he using 1 <;> push_cast <;> ring
-- CHECKPOINT

theorem enh_wrap_class_fibre_unique
    (w r A δ ε B₁ B₂ tag tag' M m₁ t₁ m₂ t₂ : ℕ)
    (hr2 : 2 ≤ r) (hr : r < w) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ / 2^r) % 2 = 1)
    (h₁ : B₁ < 2^w) (h₂ : B₂ < 2^w) (hm₁ : m₁ < 2^w)
    (hsub₁ : t₁ &&& m₁ = t₁) (hsub₂ : t₂ &&& m₂ = t₂)
    (hlabelM : m₁ % 2^(r-1) = m₂ % 2^(r-1))
    (hlabelC : Int.ModEq ((2:ℤ)^r) ((m₁:ℤ)-2*t₁) ((m₂:ℤ)-2*t₂))
    (hwrap : (B₁+ε)/2^w = (B₂+ε)/2^w)
    (hl₁ : A*B₁ % 2^w = ((A+δ)%2^w)*((B₁+ε)%2^w) % 2^w)
    (hl₂ : A*B₂ % 2^w = ((A+δ)%2^w)*((B₂+ε)%2^w) % 2^w)
    (hx₁ : enhHighNat (2^w) A B₁ tag M ^^^
      enhHighNat (2^w) ((A+δ)%2^w) ((B₁+ε)%2^w) tag' M = m₁)
    (hx₂ : enhHighNat (2^w) A B₂ tag M ^^^
      enhHighNat (2^w) ((A+δ)%2^w) ((B₂+ε)%2^w) tag' M = m₂)
    (ht₁ : enhHighNat (2^w) A B₁ tag M &&& m₁ = t₁)
    (ht₂ : enhHighNat (2^w) A B₂ tag M &&& m₂ = t₂) : B₁ = B₂ := by
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
  apply enh_signed_class_fibre_unique w r A ((A+δ)%2^w) B₁ B₂
    ((B₁+ε)%2^w) ((B₂+ε)%2^w) tag tag' M m₁ t₁ m₂ t₂ Q d e
    hr2 hRQ hd (hinc A δ hδ) (hinc B₁ ε hε)
    ?_ h₁ h₂ hm₁ hsub₁ hsub₂ hlabelM hlabelC hl₁ hl₂ hx₁ hx₂ ht₁ ht₂
  simpa only [e, hwrap] using hinc B₂ ε hε
-- CHECKPOINT

end ProvenHashes.UMASH
