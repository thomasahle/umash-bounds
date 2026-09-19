import ProvenHashes.UMASHAffineIntervals

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

def productHighSum (Q A A' ε b : ℕ) : ℕ :=
  A*b/Q+A'*((b+ε)%Q)/Q

/-- Two operand wraps and two integer representatives of the high sum
give four affine counts. No condition on the low product words is used. -/
theorem wrapped_high_sum_fiber_count (Q A A' ε t : ℕ) (S : Finset ℕ)
    (hQ : 0 < Q) (hA : A < Q) (hA' : A' < Q) (hε : ε < Q)
    (hs : 0 < A+A') (hbox : ∀ b ∈ S, b < Q)
    (hsum : ∀ b ∈ S, productHighSum Q A A' ε b%Q = t) :
    (S.card:ℚ) ≤ 4*(2*Q/(A+A':ℕ)+1) := by
  let label (b : ℕ) := ((b+ε)/Q, productHighSum Q A A' ε b/Q)
  let labels := (Finset.range 2) ×ˢ (Finset.range 2)
  let G (kj : ℕ × ℕ) := S.filter (fun b => label b = kj)
  have hlabel : ∀ b ∈ S, label b ∈ labels := by
    intro b hb
    have hbQ := hbox b hb
    have hw : (b+ε)/Q < 2 := (Nat.div_lt_iff_lt_mul hQ).mpr (by omega)
    have hh₁ : A*b/Q < Q := (Nat.div_lt_iff_lt_mul hQ).mpr (by
      nlinarith [Nat.mul_le_mul_left A hbQ.le])
    have hb' := Nat.mod_lt (b+ε) hQ
    have hh₂ : A'*((b+ε)%Q)/Q < Q := (Nat.div_lt_iff_lt_mul hQ).mpr (by
      nlinarith [Nat.mul_le_mul_left A' hb'.le])
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hw,
      Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hQ).mpr (by
        dsimp only [productHighSum]; omega))⟩
  have hcard : S.card = ∑ kj ∈ labels, (G kj).card :=
    Finset.card_eq_sum_card_fiberwise hlabel
  have hg (kj : ℕ × ℕ) : ((G kj).card:ℚ) ≤ 2*Q/(A+A':ℕ)+1 := by
    apply wrapped_high_sum_branch_count Q A A' ε kj.1 (t+Q*kj.2) (G kj) hQ hs
    · intro b hb
      exact congrArg Prod.fst (Finset.mem_filter.mp hb).2
    · intro b hb
      have hj := congrArg Prod.snd (Finset.mem_filter.mp hb).2
      have he := hsum b (Finset.mem_filter.mp hb).1
      have hr := Nat.mod_add_div (productHighSum Q A A' ε b) Q
      change productHighSum Q A A' ε b/Q = kj.2 at hj
      rw [he, hj] at hr
      exact hr.symm
  calc
    _ = ∑ kj ∈ labels, ((G kj).card:ℚ) := by exact_mod_cast hcard
    _ ≤ ∑ _kj ∈ labels, (2*Q/(A+A':ℕ)+1:ℚ) :=
      Finset.sum_le_sum (fun kj _ => hg kj)
    _ = _ := by simp [labels, Finset.card_product, nsmul_eq_mul] <;> ring
-- CHECKPOINT

/-- Summing the four affine counts over the first operand uses the
dyadic harmonic estimate, giving (4n+20)Q pairs for a fixed sum residue. -/
theorem wrapped_high_sum_count (n δ ε t : ℕ) (S : Finset (ℕ × ℕ))
    (hδ : 0 < δ ∧ δ < 2^n) (hε : ε < 2^n)
    (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hsum : ∀ ab ∈ S,
      productHighSum (2^n) ab.1 ((ab.1+δ)%2^n) ε ab.2%2^n = t) :
    (S.card:ℚ) ≤ (4*n+20:ℕ)*(2^n:ℕ) := by
  let Q := 2^n
  let G (A : ℕ) := S.filter (fun ab => ab.1 = A)
  let T (A : ℕ) := (G A).image Prod.snd
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hcard : S.card = ∑ A ∈ Finset.range Q, (G A).card :=
    Finset.card_eq_sum_card_fiberwise (fun ab hab => Finset.mem_range.mpr (hbox ab hab).1)
  have hrow (A : ℕ) (hA : A ∈ Finset.range Q) :
      ((G A).card:ℚ) ≤ 4*(2*Q/(A+(A+δ)%Q:ℕ)+1) := by
    have hAQ : A < Q := Finset.mem_range.mp hA
    have hAP : (A+δ)%Q < Q := Nat.mod_lt _ hQ
    have hs : 0 < A+(A+δ)%Q := by
      have hn := wrapped_add_ne Q A δ hAQ hδ.2 hδ.1.ne'
      omega
    have hi : Set.InjOn (Prod.snd : ℕ × ℕ → ℕ) (↑(G A)) := by
      intro x hx y hy he
      apply Prod.ext
      · exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      · exact he
    have hc : (T A).card = (G A).card := Finset.card_image_of_injOn hi
    rw [← hc]
    apply wrapped_high_sum_fiber_count Q A ((A+δ)%Q) ε t (T A) hQ hAQ hAP hε hs
    · intro b hb
      obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hb
      exact (hbox ab (Finset.mem_filter.mp hab).1).2
    · intro b hb
      obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hb
      have he := hsum ab (Finset.mem_filter.mp hab).1
      rw [(Finset.mem_filter.mp hab).2] at he
      exact he
  have hrec := wrapped_reciprocal_sum n δ hδ.2
  have htotal : (∑ A ∈ Finset.range Q, (4*(2*Q/(A+(A+δ)%Q:ℕ)+1):ℚ)) =
      8*Q*(∑ A ∈ Finset.range Q, (1:ℚ)/(A+(A+δ)%Q:ℕ))+4*Q := by
    simp_rw [show ∀ A : ℕ, (4*(2*Q/(A+(A+δ)%Q:ℕ)+1):ℚ) =
      (8*Q)*((1:ℚ)/(A+(A+δ)%Q:ℕ))+4 by intro A; ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [mul_comm]
  calc
    _ = ∑ A ∈ Finset.range Q, ((G A).card:ℚ) := by exact_mod_cast hcard
    _ ≤ ∑ A ∈ Finset.range Q, (4*(2*Q/(A+(A+δ)%Q:ℕ)+1):ℚ) :=
      Finset.sum_le_sum hrow
    _ = 8*Q*(∑ A ∈ Finset.range Q, (1:ℚ)/(A+(A+δ)%Q:ℕ))+4*Q := htotal
    _ ≤ 8*Q*((n:ℚ)/2+2)+4*Q := by gcongr
    _ = _ := by dsimp only [Q]; push_cast; ring
-- CHECKPOINT

end ProvenHashes.UMASH
