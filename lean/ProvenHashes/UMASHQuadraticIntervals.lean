import ProvenHashes.UMASHIntervalPacking

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- Integer preimages on the right side of the vertex. The output
intervals are handled together, before taking a square root. -/
theorem parabola_right_interval_count (m : ℕ) (lo hi : Fin m → ℝ)
    (ell a c v : ℝ) (T : Finset ℤ) (hell : 0 ≤ ell) (ha : a ≠ 0)
    (hlen : ∀ i, hi i-lo i ≤ ell)
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.Ico (lo i) (hi i)) (Set.Ico (lo j) (hi j)))
    (hside : ∀ t ∈ T, v ≤ (t:ℝ))
    (hcover : ∀ t ∈ T, ∃ i, lo i ≤ a*((t:ℝ)-v)^2+c ∧
      a*((t:ℝ)-v)^2+c < hi i) :
    (T.card:ℝ) ≤ Real.sqrt ((m:ℝ)*ell/|a|)+m := by
  classical
  let G : Fin m → Finset ℤ := fun i => T.filter (fun t =>
    lo i ≤ a*((t:ℝ)-v)^2+c ∧ a*((t:ℝ)-v)^2+c < hi i)
  have hdata := fun i => integer_span_data (G i) v
    (fun t ht => hside t (Finset.mem_filter.mp ht).1)
  choose l u hl hle hc he using hdata
  have hsq (i : Fin m) : (u i)^2-(l i)^2 ≤ ell/|a| := by
    rcases he i with ⟨_, hli, hui⟩ | ⟨x, hx, y, hy, hli, hui⟩
    · rw [hli, hui]
      simpa using div_nonneg hell (abs_nonneg a)
    · apply parabola_span_sq_le a c ell (lo i) (hi i) (l i) (u i) ha (hlen i)
      · simpa only [hli] using (Finset.mem_filter.mp hx).2
      · simpa only [hui] using (Finset.mem_filter.mp hy).2
  have hordered : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ∀ j ∈ (Finset.univ : Finset (Fin m)), i ≠ j →
        u i ≤ l j ∨ u j ≤ l i := by
    intro i _ j _ hij
    rcases he i with ⟨_, _, hui⟩ | ⟨x, hx, y, hy, hli, hui⟩
    · exact Or.inl (by simpa [hui] using hl j)
    rcases he j with ⟨_, _, huj⟩ | ⟨x', hx', y', hy', hlj, huj⟩
    · exact Or.inr (by simpa [huj] using hl i)
    apply parabola_spans_ordered a c (lo i) (hi i) (lo j) (hi j)
      (l i) (u i) (l j) (u j) ha ⟨hl i, hle i⟩ ⟨hl j, hle j⟩
    · simpa only [hli] using (Finset.mem_filter.mp hx).2
    · simpa only [hui] using (Finset.mem_filter.mp hy).2
    · simpa only [hlj] using (Finset.mem_filter.mp hx').2
    · simpa only [huj] using (Finset.mem_filter.mp hy').2
    · exact hdis i j hij
  have hpack : (∑ i, (u i-l i))^2 ≤ (m:ℝ)*ell/|a| := by
    calc
      _ ≤ ∑ i, ((u i)^2-(l i)^2) :=
        interval_packing_sq Finset.univ l u (fun i _ => ⟨hl i, hle i⟩) hordered
      _ ≤ ∑ _i : Fin m, ell/|a| := Finset.sum_le_sum (fun i _ => hsq i)
      _ = (m:ℝ)*ell/|a| := by simp [mul_div_assoc]
  have hroot := Real.le_sqrt_of_sq_le hpack
  have hsubset : T ⊆ Finset.univ.biUnion G := by
    intro t ht
    obtain ⟨i, hi⟩ := hcover t ht
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨ht, hi⟩⟩
  have hcard : T.card ≤ ∑ i, (G i).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hcardR : (T.card:ℝ) ≤ ∑ i, ((G i).card:ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ ∑ i, ((G i).card:ℝ) := hcardR
    _ ≤ ∑ i, (u i-l i+1) := Finset.sum_le_sum (fun i _ => hc i)
    _ = (∑ i, (u i-l i))+(m:ℝ) := by simp [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add_right hroot _
-- CHECKPOINT

/-- Both sides of the vertex, with the vertex allowed in both counts. -/
theorem parabola_interval_count (m : ℕ) (lo hi : Fin m → ℝ)
    (ell a c v : ℝ) (T : Finset ℤ) (hell : 0 ≤ ell) (ha : a ≠ 0)
    (hlen : ∀ i, hi i-lo i ≤ ell)
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.Ico (lo i) (hi i)) (Set.Ico (lo j) (hi j)))
    (hcover : ∀ t ∈ T, ∃ i, lo i ≤ a*((t:ℝ)-v)^2+c ∧
      a*((t:ℝ)-v)^2+c < hi i) :
    (T.card:ℝ) ≤ 2*Real.sqrt ((m:ℝ)*ell/|a|)+2*m := by
  classical
  let R : Finset ℤ := T.filter (fun t : ℤ => v ≤ (t:ℝ))
  let L : Finset ℤ := T.filter (fun t : ℤ => (t:ℝ) ≤ v)
  let N := L.image (fun t : ℤ => -t)
  have hR := parabola_right_interval_count m lo hi ell a c v R hell ha hlen hdis
    (fun t ht => (Finset.mem_filter.mp ht).2)
    (fun t ht => hcover t (Finset.mem_filter.mp ht).1)
  have hN : (N.card:ℝ) ≤ Real.sqrt ((m:ℝ)*ell/|a|)+m := by
    apply parabola_right_interval_count m lo hi ell a c (-v) N hell ha hlen hdis
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      have hu := (Finset.mem_filter.mp hu).2
      push_cast
      linarith
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨i, hi⟩ := hcover u (Finset.mem_filter.mp hu).1
      have heq : a*(((-u:ℤ):ℝ)- -v)^2+c = a*((u:ℝ)-v)^2+c := by
        push_cast
        ring
      exact ⟨i, by simpa only [heq] using hi⟩
  have hcardN : N.card = L.card := Finset.card_image_of_injective _ neg_injective
  have hsub : T ⊆ R ∪ L := by
    intro t ht
    rcases le_total v (t:ℝ) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, h⟩)
  have hc : T.card ≤ R.card+L.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le R L)
  have hcR : (T.card:ℝ) ≤ (R.card:ℝ)+(L.card:ℝ) := by exact_mod_cast hc
  rw [hcardN] at hN
  linarith
-- CHECKPOINT

/-- PROOF2 Lemma 4.1, with every hypothesis from the recorded obligation
and no additional analytic assumption. -/
theorem quadratic_interval_count : QuadraticIntervalCount := by
  intro m lo hi ell a b c T _hm hell ha hlen hdis hcover
  have haR : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  let v : ℝ := -(b:ℝ)/(2*(a:ℝ))
  let C : ℝ := (c:ℝ)-(b:ℝ)^2/(4*(a:ℝ))
  have hcomplete (t : ℤ) :
      (quadraticValue a b c t:ℝ) = (a:ℝ)*((t:ℝ)-v)^2+C := by
    dsimp only [quadraticValue, v, C]
    push_cast
    field_simp
    <;> ring
  apply parabola_interval_count m lo hi ell a C v T hell.le haR
    (fun i => (hlen i).2) hdis
  intro t ht
  obtain ⟨i, hi⟩ := hcover t ht
  exact ⟨i, by simpa only [hcomplete t] using hi⟩
-- CHECKPOINT

end ProvenHashes.UMASH
