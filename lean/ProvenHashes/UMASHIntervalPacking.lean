import ProvenHashes.UMASHContinuationObligations

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- Removing gaps between nonnegative intervals only decreases the sum of
their squared endpoint differences. The first conclusion supplies the
induction invariant needed for the second. -/
theorem interval_packing_strict {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hpos : ∀ i ∈ s, 0 ≤ lo i ∧ lo i < hi i)
    (hbound : ∀ i ∈ s, hi i ≤ B)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i) :
    (∑ i ∈ s, (hi i-lo i)) ≤ B ∧
      (∑ i ∈ s, (hi i-lo i))^2 ≤ ∑ i ∈ s, ((hi i)^2-(lo i)^2) := by
  classical
  induction s using Finset.induction_on_max_value hi generalizing B with
  | h0 => simp [hB]
  | step i s his hmax ih =>
    have hipos := hpos i (Finset.mem_insert_self _ _)
    have hsub : ∀ j ∈ s, hi j ≤ lo i := by
      intro j hj
      rcases hdis i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (by intro he; subst j; exact his hj) with h | h
      · have hjpos := hpos j (Finset.mem_insert_of_mem hj)
        have hjmax := hmax j hj
        linarith
      · exact h
    have hrec := ih (lo i) hipos.1
      (fun j hj => hpos j (Finset.mem_insert_of_mem hj)) hsub
      (fun j hj k hk => hdis j (Finset.mem_insert_of_mem hj)
        k (Finset.mem_insert_of_mem hk))
    have hib := hbound i (Finset.mem_insert_self _ _)
    simp only [Finset.sum_insert his]
    constructor
    · linarith [hrec.1]
    · nlinarith [hrec.1, hrec.2]
-- CHECKPOINT

/-- The squared-width packing inequality also allows singleton intervals. -/
theorem interval_packing_sq {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 ≤ lo i ∧ lo i ≤ hi i)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i) :
    (∑ i ∈ s, (hi i-lo i))^2 ≤ ∑ i ∈ s, ((hi i)^2-(lo i)^2) := by
  classical
  let t := s.filter (fun i => lo i < hi i)
  have ht : t ⊆ s := Finset.filter_subset _ _
  have hzero (i : ι) (hiS : i ∈ s) (hiT : i ∉ t) : hi i = lo i := by
    have h := hpos i hiS
    have hn : ¬lo i < hi i := by simpa [t, hiS] using hiT
    linarith
  have hsum : (∑ i ∈ t, (hi i-lo i)) = ∑ i ∈ s, (hi i-lo i) := by
    exact Finset.sum_subset ht (fun i his hit => by rw [hzero i his hit, sub_self])
  have hsq : (∑ i ∈ t, ((hi i)^2-(lo i)^2)) =
      ∑ i ∈ s, ((hi i)^2-(lo i)^2) := by
    exact Finset.sum_subset ht (fun i his hit => by rw [hzero i his hit, sub_self])
  have hnonneg : ∀ i ∈ t, 0 ≤ hi i := fun i hiT =>
    (hpos i (ht hiT)).1.trans (hpos i (ht hiT)).2
  have hp := interval_packing_strict t lo hi (∑ i ∈ t, hi i)
    (Finset.sum_nonneg hnonneg)
    (fun i hiT => ⟨(hpos i (ht hiT)).1, (Finset.mem_filter.mp hiT).2⟩)
    (fun i hiT => Finset.single_le_sum hnonneg hiT)
    (fun i hiT j hjT => hdis i (ht hiT) j (ht hjT))
  simpa only [hsum, hsq] using hp.2
-- CHECKPOINT

/-- A finite set of integers on one side of a real origin has a span of
length at least its cardinality minus one. Empty sets receive the zero span. -/
theorem integer_span_data (T : Finset ℤ) (v : ℝ)
    (hside : ∀ t ∈ T, v ≤ (t:ℝ)) :
    ∃ l u : ℝ, 0 ≤ l ∧ l ≤ u ∧ (T.card:ℝ) ≤ u-l+1 ∧
      ((T = ∅ ∧ l = 0 ∧ u = 0) ∨
        ∃ x ∈ T, ∃ y ∈ T, l = (x:ℝ)-v ∧ u = (y:ℝ)-v) := by
  classical
  rcases T.eq_empty_or_nonempty with hT | hT
  · subst T
    exact ⟨0, 0, le_rfl, le_rfl, by simp, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · let x := T.min' hT
    let y := T.max' hT
    have hx : x ∈ T := T.min'_mem hT
    have hy : y ∈ T := T.max'_mem hT
    have hxy : x ≤ y := T.min'_le y hy
    have hcard : T.card ≤ (Finset.Icc x y).card := by
      apply Finset.card_le_card
      intro z hz
      exact Finset.mem_Icc.mpr ⟨T.min'_le z hz, T.le_max' z hz⟩
    have hc : (T.card:ℤ) ≤ y+1-x := by
      calc
        (T.card:ℤ) ≤ ((Finset.Icc x y).card:ℤ) := by exact_mod_cast hcard
        _ = y+1-x := Int.card_Icc_of_le x y (by omega)
    have hcR : (T.card:ℝ) ≤ (y:ℝ)+1-x := by exact_mod_cast hc
    have hxyR : (x:ℝ) ≤ y := by exact_mod_cast hxy
    refine ⟨(x:ℝ)-v, (y:ℝ)-v, sub_nonneg.mpr (hside x hx),
      sub_le_sub_right hxyR v, ?_, Or.inr ⟨x, hx, y, hy, rfl, rfl⟩⟩
    linarith
-- CHECKPOINT

/-- Two points of a parabola in one output interval consume at most that
interval's width, after division by the absolute leading coefficient. -/
theorem parabola_span_sq_le (a c ell L H l u : ℝ) (ha : a ≠ 0)
    (hlen : H-L ≤ ell)
    (hl : L ≤ a*l^2+c ∧ a*l^2+c < H)
    (hu : L ≤ a*u^2+c ∧ a*u^2+c < H) :
    u^2-l^2 ≤ ell/|a| := by
  apply (le_div_iff₀ (abs_pos.mpr ha)).mpr
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [abs_of_neg ha]
    nlinarith [hl.1, hu.2]
  · rw [abs_of_pos ha]
    nlinarith [hu.1, hl.2, hu.2, hl.1]
-- CHECKPOINT

/-- Disjoint output intervals give ordered input spans on a single side of
any nonconstant parabola, including a negative leading coefficient. -/
theorem parabola_spans_ordered (a c L H L' H' l u l' u' : ℝ)
    (ha : a ≠ 0) (hlu : 0 ≤ l ∧ l ≤ u) (hlu' : 0 ≤ l' ∧ l' ≤ u')
    (hl : L ≤ a*l^2+c ∧ a*l^2+c < H)
    (hu : L ≤ a*u^2+c ∧ a*u^2+c < H)
    (hl' : L' ≤ a*l'^2+c ∧ a*l'^2+c < H')
    (hu' : L' ≤ a*u'^2+c ∧ a*u'^2+c < H')
    (hdis : Disjoint (Set.Ico L H) (Set.Ico L' H')) :
    u ≤ l' ∨ u' ≤ l := by
  have hLH : L < H := hl.1.trans_lt hl.2
  have hLH' : L' < H' := hl'.1.trans_lt hl'.2
  have hsep : H ≤ L' ∨ H' ≤ L := by
    have hd := Set.Ico_disjoint_Ico.mp hdis
    simp only [min_le_iff, le_max_iff] at hd
    rcases hd with (h | h) | (h | h)
    · exact False.elim (not_le_of_gt hLH h)
    · exact Or.inr h
    · exact Or.inl h
    · exact False.elim (not_le_of_gt hLH' h)
  rcases hsep with hsep | hsep
  · rcases lt_or_gt_of_ne ha with hneg | hpos
    · right
      have hmul : (-a)*u'^2 < (-a)*l^2 := by linarith [hl.2, hu'.1]
      have hs := (mul_lt_mul_iff_right₀ (neg_pos.mpr hneg)).mp hmul
      nlinarith [hlu.1, hlu'.1, hlu'.2]
    · left
      have hmul : a*u^2 < a*l'^2 := by linarith [hu.2, hl'.1]
      have hs := (mul_lt_mul_iff_right₀ hpos).mp hmul
      nlinarith [hlu.1, hlu.2, hlu'.1]
  · rcases lt_or_gt_of_ne ha with hneg | hpos
    · left
      have hmul : (-a)*u^2 < (-a)*l'^2 := by linarith [hl'.2, hu.1]
      have hs := (mul_lt_mul_iff_right₀ (neg_pos.mpr hneg)).mp hmul
      nlinarith [hlu.1, hlu.2, hlu'.1]
    · right
      have hmul : a*u'^2 < a*l^2 := by linarith [hu'.2, hl.1]
      have hs := (mul_lt_mul_iff_right₀ hpos).mp hmul
      nlinarith [hlu.1, hlu'.1, hlu'.2]
-- CHECKPOINT

end ProvenHashes.UMASH
