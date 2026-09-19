import ProvenHashes.UMASHQuadraticIntervals

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- The integer parameter on a primitive line is recovered by a named
division. Both coordinates are reconstructed from that parameter. -/
theorem coprime_line_coordinate (a b x₀ y₀ x y : ℤ)
    (ha : a ≠ 0) (hab : Int.gcd a b = 1)
    (heq : a*y+b*x = a*y₀+b*x₀) :
    x = x₀+a*((x-x₀)/a) ∧ y = y₀-b*((x-x₀)/a) := by
  have hd : a ∣ b*(x-x₀) := ⟨y₀-y, by nlinarith [heq]⟩
  have hdiv : a ∣ x-x₀ := Int.dvd_of_dvd_mul_right_of_gcd_one hd hab
  have hx : x = x₀+a*((x-x₀)/a) := by
    have hc := Int.ediv_mul_cancel hdiv
    nlinarith [hc]
  refine ⟨hx, ?_⟩
  apply mul_left_cancel₀ ha
  rw [hx] at heq
  nlinarith [heq]
-- CHECKPOINT

/-- Products on a primitive integer line form a nonconstant integer
quadratic in the recovered parameter. -/
theorem coprime_line_product_interval_count
    (m : ℕ) (lo hi : Fin m → ℝ) (ell : ℝ) (a b d : ℤ) (S : Finset (ℤ × ℤ))
    (hm : 0 < m) (hell : 0 < ell) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : Int.gcd a b = 1)
    (hline : ∀ z ∈ S, a*z.2+b*z.1 = d)
    (hlen : ∀ i, lo i ≤ hi i ∧ hi i-lo i ≤ ell)
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.Ico (lo i) (hi i)) (Set.Ico (lo j) (hi j)))
    (hcover : ∀ z ∈ S, ∃ i, lo i ≤ ((z.1*z.2:ℤ):ℝ) ∧
      ((z.1*z.2:ℤ):ℝ) < hi i) :
    (S.card:ℝ) ≤ 2*Real.sqrt ((m:ℝ)*ell/|((-a*b:ℤ):ℝ)|)+2*m := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨z₀, hz₀⟩ := hS
  let f : ℤ × ℤ → ℤ := fun z => (z.1-z₀.1)/a
  have hcoords (z : ℤ × ℤ) (hz : z ∈ S) :
      z.1 = z₀.1+a*f z ∧ z.2 = z₀.2-b*f z :=
    coprime_line_coordinate a b z₀.1 z₀.2 z.1 z.2 ha hab
      ((hline z hz).trans (hline z₀ hz₀).symm)
  have hf : Set.InjOn f S := by
    intro x hx y hy hxy
    have hxc := hcoords x hx
    have hyc := hcoords y hy
    exact Prod.ext (by rw [hxc.1, hyc.1, hxy]) (by rw [hxc.2, hyc.2, hxy])
  have hcard : (S.image f).card = S.card := Finset.card_image_iff.mpr hf
  have hpoly (z : ℤ × ℤ) (hz : z ∈ S) :
      quadraticValue (-a*b) (a*z₀.2-b*z₀.1) (z₀.1*z₀.2) (f z) = z.1*z.2 := by
    have hc := hcoords z hz
    calc
      _ = (z₀.1+a*f z)*(z₀.2-b*f z) := by unfold quadraticValue; ring
      _ = z.1*z.2 := by rw [← hc.1, ← hc.2]
  have hquad := quadratic_interval_count m lo hi ell (-a*b)
    (a*z₀.2-b*z₀.1) (z₀.1*z₀.2) (S.image f) hm hell
    (mul_ne_zero (neg_ne_zero.mpr ha) hb) hlen hdis
    (by
      intro t ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
      simpa only [hpoly z hz] using hcover z hz)
  simpa only [hcard] using hquad
-- CHECKPOINT

/-- The line count in PROOF2 Lemma 4.2, with arbitrary nonzero signed
increments. Dividing by their gcd gives a quadratic coefficient of absolute
value at least one. -/
theorem integer_line_product_interval_count
    (m : ℕ) (lo hi : Fin m → ℝ) (ell : ℝ) (a b d : ℤ) (S : Finset (ℤ × ℤ))
    (hm : 0 < m) (hell : 0 < ell) (ha : a ≠ 0) (hb : b ≠ 0)
    (hline : ∀ z ∈ S, a*z.2+b*z.1 = d)
    (hlen : ∀ i, lo i ≤ hi i ∧ hi i-lo i ≤ ell)
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.Ico (lo i) (hi i)) (Set.Ico (lo j) (hi j)))
    (hcover : ∀ z ∈ S, ∃ i, lo i ≤ ((z.1*z.2:ℤ):ℝ) ∧
      ((z.1*z.2:ℤ):ℝ) < hi i) :
    (S.card:ℝ) ≤ 2*Real.sqrt ((m:ℝ)*ell)+2*m := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨z₀, hz₀⟩ := hS
  have hg : 0 < Int.gcd a b := Int.gcd_pos_of_ne_zero_left b ha
  obtain ⟨u, v, huv, hau, hbv⟩ := Int.exists_gcd_one hg
  have hu : u ≠ 0 := by intro h; apply ha; simpa only [h, zero_mul] using hau
  have hv : v ≠ 0 := by intro h; apply hb; simpa only [h, zero_mul] using hbv
  have hgZ : (Int.gcd a b:ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hline' (z : ℤ × ℤ) (hz : z ∈ S) : u*z.2+v*z.1 = u*z₀.2+v*z₀.1 := by
    apply mul_right_cancel₀ hgZ
    calc
      _ = (u*(Int.gcd a b:ℤ))*z.2+(v*(Int.gcd a b:ℤ))*z.1 := by ring
      _ = a*z.2+b*z.1 := by rw [← hau, ← hbv]
      _ = a*z₀.2+b*z₀.1 := (hline z hz).trans (hline z₀ hz₀).symm
      _ = (u*(Int.gcd a b:ℤ))*z₀.2+(v*(Int.gcd a b:ℤ))*z₀.1 := by
        rw [← hau, ← hbv]
      _ = _ := by ring
  have hc := coprime_line_product_interval_count m lo hi ell u v
    (u*z₀.2+v*z₀.1) S hm hell hu hv huv hline' hlen hdis hcover
  have hp : (0:ℤ) < |-u*v| := abs_pos.mpr (mul_ne_zero (neg_ne_zero.mpr hu) hv)
  have hge : (1:ℤ) ≤ |-u*v| := by omega
  have hgeR : (1:ℝ) ≤ |((-u*v:ℤ):ℝ)| := by exact_mod_cast hge
  have hdiv : (m:ℝ)*ell/|((-u*v:ℤ):ℝ)| ≤ (m:ℝ)*ell :=
    div_le_self (by positivity) hgeR
  have hsqrt := Real.sqrt_le_sqrt hdiv
  linarith
-- CHECKPOINT

end ProvenHashes.UMASH
