import ProvenHashes.UMASHOneWordCoordinates

/-! One-word ENH high atoms, using the argument from the GPT-6 Pro handoff
of 2026-09-19, earlier ENH notes §4. All widths and all fixed tags are covered. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

theorem one_word_high_count (n v δ tag tag' e : ℕ)
    (hv : v < n) (hd : 2^v ∣ δ) (ho : (δ/2^v)%2 = 1)
    (S : Finset (ℕ × ℕ)) (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, highXorEventNat n δ 0 tag tag' e ab) :
    S.card ≤ (2*v+1)*2^n := by
  let N := 2^(n-v)
  have hN : 0 < N := by positivity
  have hMN : 2^v*N = 2^n := by dsimp [N]; rw [← pow_add,Nat.add_sub_of_le hv.le]
  have hdiv (ab : ℕ × ℕ) (hab : ab ∈ S) : N ∣ ab.2 := by
    apply one_word_low_multiple n v δ ab.1 ab.2 hv.le hd ho
    simpa only [Nat.add_zero,Nat.mod_eq_of_lt (hbox ab hab).2] using (hevent ab hab).1
  let f (ab : ℕ × ℕ) := (ab.1,ab.2/N)
  have hinj : Set.InjOn f (↑S : Set (ℕ × ℕ)) := by
    intro ab hab ab' hab' he
    have hfst := congrArg Prod.fst he
    change ab.1 = ab'.1 at hfst
    apply Prod.ext hfst
    have hh := congrArg (fun z : ℕ × ℕ => N*z.2) he
    simpa only [f,Nat.mul_div_cancel' (hdiv ab hab),Nat.mul_div_cancel' (hdiv ab' hab')] using hh
  rw [← Finset.card_image_of_injOn hinj]
  apply one_word_coordinate_count n v hv.le (fun j => (j+δ/2^v)%N) tag tag' e
    (fun j _ => one_word_next_odd n v (δ/2^v) hv ho j) (S.image f)
  · intro az haz
    obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp haz
    refine ⟨(hbox ab hab).1, ?_⟩
    dsimp only [f]
    exact (Nat.div_lt_iff_lt_mul hN).mpr (hMN ▸ (hbox ab hab).2)
  · intro az haz
    obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp haz
    exact one_word_event_to_coordinates n v δ tag tag' e ab.1 ab.2 hv.le hd
      (hbox ab hab).2 (hdiv ab hab) (hevent ab hab)
-- CHECKPOINT

theorem one_word_high_probability (n v δ tag tag' e : ℕ)
    (hv : v < n) (hd : 2^v ∣ δ) (ho : (δ/2^v)%2 = 1) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      highXorEventNat n δ 0 tag tag' e (ab.1.val,ab.2.val)) ≤
      (2*v+1:ℕ)/((2:ℚ≥0)^n) := by
  have hc := fin_pair_probability_of_nat_count (2^n) ((2*v+1)*2^n)
    (highXorEventNat n δ 0 tag tag' e)
    (fun S hb hE => one_word_high_count n v δ tag tag' e hv hd ho S hb hE)
  calc
    _ ≤ ((2*v+1:ℕ):ℚ≥0)*((2:ℚ≥0)^n)/((2:ℚ≥0)^n)^2 := by
      simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hc
    _ = _ := by field_simp
-- CHECKPOINT

theorem one_word_high_probability_word (δ tag tag' e : ℕ) (hδ : 0 < δ ∧ δ < q) :
    uniformProb (fun ab : Chunk => highXorEventNat 64 δ 0 tag tag' e
      (ab.1.toNat,ab.2.toNat)) ≤ (127:ℚ≥0)/q := by
  obtain ⟨hv,hd,ho⟩ := dyadic_increment_padic_factor 64 δ hδ
  let equiv : (Fin (2^64) × Fin (2^64)) ≃ Chunk :=
    Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv equiv]
  exact (one_word_high_probability 64 (padicValNat 2 δ) δ tag tag' e hv hd ho).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast (show 2*padicValNat 2 δ+1 ≤ 127 by omega)) (by positivity))
-- CHECKPOINT

end ProvenHashes.UMASH
