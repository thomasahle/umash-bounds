import ProvenHashes.UMASHLowWidth

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

/-- Fixing the low product and transformed coordinate gives a quadratic
congruence in the first operand, at every width. -/
theorem low_coordinate_value_congruence (n r a b A B C Y : ℕ)
    (hC : lowCoordinate n r a b A B = C) (hY : A*B%2^n = Y) :
    Int.ModEq ((2:ℤ)^n)
      (-(b:ℤ)*(A:ℤ)^2+((C:ℤ)-(2:ℤ)^r*a*b)*A) ((a:ℤ)*Y) := by
  have hc : Int.ModEq ((2:ℤ)^n)
      ((a:ℤ)*B+(b:ℤ)*A+(2:ℤ)^r*a*b) (C:ℤ) := by
    rw [← hC]
    simpa only [lowCoordinate, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (Int.natCast_modEq_iff.mpr (Nat.mod_mod (a*B+b*A+2^r*a*b) (2^n)).symm)
  have hy : Int.ModEq ((2:ℤ)^n) ((A:ℤ)*B) (Y:ℤ) := by
    rw [← hY]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (Int.natCast_modEq_iff.mpr (Nat.mod_mod (A*B) (2^n)).symm)
  have hquad : Int.ModEq ((2:ℤ)^n) ((a:ℤ)*((A:ℤ)*B))
      (-(b:ℤ)*(A:ℤ)^2+((C:ℤ)-(2:ℤ)^r*a*b)*A) := by
    convert ((hc.sub_right ((2:ℤ)^r*a*b)).mul_right (A:ℤ)).add_left
      (-(b:ℤ)*(A:ℤ)^2) using 1 <;> ring
  exact hquad.symm.trans (hy.mul_left (a:ℤ))
-- CHECKPOINT

/-- For a target of exactly the minimum valuation, the transformed
quadratic has odd linear coefficient. No nonzero second increment is needed. -/
theorem low_coordinate_minimal_odd (n r a b e Y C : ℕ)
    (he : 0 < e ∧ e < 2^n) (hr : r = padicValNat 2 e) (hr1 : 1 ≤ r)
    (hC : Int.ModEq ((2:ℤ)^n) ((2:ℤ)^r*C) ((e:ℤ)-2*(Y &&& e:ℕ))) :
    ((C:ℤ)-(2:ℤ)^r*a*b)%2 = 1 := by
  have hz : (Y &&& e) &&& e = Y &&& e := by rw [Nat.and_assoc, Nat.and_self]
  have hv := low_coordinate_exact_valuation n r e (Y &&& e) C he hz hr.le hC
  have hn : ¬(2:ℤ) ∣ (C:ℤ) := by simpa only [← hr, Nat.sub_self, Nat.zero_add, pow_one] using hv.2
  have hodd : (C:ℤ)%2 = 1 := by
    rw [Int.dvd_iff_emod_eq_zero] at hn
    omega
  have hp : (2:ℤ)^r%2 = 0 := by
    apply Int.emod_eq_zero_of_dvd
    exact dvd_pow_self (2:ℤ) (by omega)
  have hm : ((2:ℤ)^r*a*b)%2 = 0 := by simp [Int.mul_emod, hp]
  rw [Int.sub_emod, hm, hodd]
  norm_num
-- CHECKPOINT

/-- A fixed low product and coordinate have at most two operand pairs. -/
theorem low_coordinate_minimal_fibre_count (n r a b e Y C : ℕ)
    (he : 0 < e ∧ e < 2^n) (hr : r = padicValNat 2 e) (hr1 : 1 ≤ r)
    (ha : a%2 = 1)
    (hC : Int.ModEq ((2:ℤ)^n) ((2:ℤ)^r*C) ((e:ℤ)-2*(Y &&& e:ℕ)))
    (S : Finset (ℕ × ℕ)) (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hcoord : ∀ ab ∈ S, lowCoordinate n r a b ab.1 ab.2 = C)
    (hprod : ∀ ab ∈ S, ab.1*ab.2%2^n = Y) : S.card ≤ 2 := by
  have hc := low_coordinate_minimal_odd n r a b e Y C he hr hr1 hC
  calc
    S.card ≤ (Finset.range 2).card := by
      apply Finset.card_le_card_of_injOn (fun ab : ℕ × ℕ => ab.1%2)
      · intro ab _
        exact Finset.mem_range.mpr (Nat.mod_lt _ (by decide))
      · intro x hx y hy hpar
        have hqx := low_coordinate_value_congruence n r a b x.1 x.2 C Y
          (hcoord x hx) (hprod x hx)
        have hqy := low_coordinate_value_congruence n r a b y.1 y.2 C Y
          (hcoord y hy) (hprod y hy)
        have hA : x.1 = y.1 := quadratic_odd_linear_parity_unique n x.1 y.1
          (-(b:ℤ)) ((C:ℤ)-(2:ℤ)^r*a*b) 0 hc (hbox x hx).1 (hbox y hy).1 hpar
          (by simpa only [add_zero] using hqx.trans hqy.symm)
        apply Prod.ext hA
        have hm : Nat.ModEq (2^n) (a*x.2+b*x.1+2^r*a*b) (a*y.2+b*y.1+2^r*a*b) :=
          (hcoord x hx).trans (hcoord y hy).symm
        have hm' := hm.add_right_cancel' (2^r*a*b)
        rw [hA] at hm'
        have hm'' := hm'.add_right_cancel' (b*y.1)
        have hac : Nat.Coprime (2^n) a :=
          ((Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ha)).pow_right n).symm
        have hh := Nat.ModEq.cancel_left_of_coprime hac hm''
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hbox x hx).2,
          Nat.mod_eq_of_lt (hbox y hy).2] using hh
    _ = _ := Finset.card_range _
-- CHECKPOINT

/-- Each prescribed low product has at most 2^r coordinate lifts. -/
theorem low_xor_minimal_value_count (n r a b e Y : ℕ)
    (he : 0 < e ∧ e < 2^n) (hr : r = padicValNat 2 e) (hr1 : 1 ≤ r)
    (ha : a%2 = 1) (S : Finset (ℕ × ℕ))
    (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, lowENHXor n (2^r*a) (2^r*b) ab.1 ab.2 = e)
    (hprod : ∀ ab ∈ S, ab.1*ab.2%2^n = Y) : S.card ≤ 2^r*2 := by
  let T := (Finset.range (2^n)).filter (fun C : ℕ =>
    Int.ModEq ((2:ℤ)^n) ((2:ℤ)^r*C) ((e:ℤ)-2*(Y &&& e:ℕ)))
  let G (C : ℕ) := S.filter (fun ab => lowCoordinate n r a b ab.1 ab.2 = C)
  have hv : r < n := by rw [hr]; exact (dyadic_increment_padic_factor n e he).1
  have hT : T.card ≤ 2^r := scaled_coordinate_lift_count n r ((e:ℤ)-2*(Y &&& e:ℕ)) T hv.le
    (fun C hC => Finset.mem_range.mp (Finset.mem_filter.mp hC).1)
    (fun C hC => (Finset.mem_filter.mp hC).2)
  have hlabel (ab : ℕ × ℕ) (hab : ab ∈ S) : lowCoordinate n r a b ab.1 ab.2 ∈ T := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by positivity)), ?_⟩
    simpa only [hprod ab hab] using
      low_coordinate_residue_congruence n r a b ab.1 ab.2 e (hevent ab hab)
  have hf (C : ℕ) (hC : C ∈ T) : (G C).card ≤ 2 := by
    apply low_coordinate_minimal_fibre_count n r a b e Y C he hr hr1 ha
      (Finset.mem_filter.mp hC).2 (G C)
    · intro ab hab
      exact hbox ab (Finset.mem_filter.mp hab).1
    · intro ab hab
      exact (Finset.mem_filter.mp hab).2
    · intro ab hab
      exact hprod ab (Finset.mem_filter.mp hab).1
  calc
    S.card = ∑ C ∈ T, (G C).card := Finset.card_eq_sum_card_fiberwise hlabel
    _ ≤ ∑ _C ∈ T, 2 := Finset.sum_le_sum hf
    _ = T.card*2 := by simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hT
-- CHECKPOINT

/-- PROOF3 Lemma 3.1(c) as a width-uniform integer count. -/
theorem low_xor_minimal_count (n r a b e : ℕ)
    (he : 0 < e ∧ e < 2^n) (hr : r = padicValNat 2 e) (hr1 : 1 ≤ r)
    (ha : a%2 = 1) (S : Finset (ℕ × ℕ))
    (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, lowENHXor n (2^r*a) (2^r*b) ab.1 ab.2 = e) :
    S.card ≤ 2^(r+1)*2^n := by
  let G (Y : ℕ) := S.filter (fun ab => ab.1*ab.2%2^n = Y)
  have hlabel (ab : ℕ × ℕ) (_hab : ab ∈ S) : ab.1*ab.2%2^n ∈ Finset.range (2^n) :=
    Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
  have hf (Y : ℕ) (_hY : Y ∈ Finset.range (2^n)) : (G Y).card ≤ 2^r*2 :=
    low_xor_minimal_value_count n r a b e Y he hr hr1 ha (G Y)
      (fun ab hab => hbox ab (Finset.mem_filter.mp hab).1)
      (fun ab hab => hevent ab (Finset.mem_filter.mp hab).1)
      (fun ab hab => (Finset.mem_filter.mp hab).2)
  calc
    S.card = ∑ Y ∈ Finset.range (2^n), (G Y).card := Finset.card_eq_sum_card_fiberwise hlabel
    _ ≤ ∑ _Y ∈ Finset.range (2^n), 2^r*2 := Finset.sum_le_sum hf
    _ = 2^(r+1)*2^n := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, pow_succ]; ring
-- CHECKPOINT

theorem low_xor_minimal_probability (n r a b e : ℕ)
    (he : 0 < e ∧ e < 2^n) (hr : r = padicValNat 2 e) (hr1 : 1 ≤ r)
    (ha : a%2 = 1) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      lowENHXor n (2^r*a) (2^r*b) ab.1.val ab.2.val = e) ≤
      (2:ℚ≥0)^(r+1)/(2:ℚ≥0)^n := by
  have hc := fin_pair_probability_of_nat_count (2^n) (2^(r+1)*2^n)
    (fun ab => lowENHXor n (2^r*a) (2^r*b) ab.1 ab.2 = e)
    (fun S hb hE => low_xor_minimal_count n r a b e he hr hr1 ha S hb hE)
  calc
    _ ≤ ((2:ℚ≥0)^(r+1)*(2:ℚ≥0)^n)/((2:ℚ≥0)^n)^2 := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
    _ = _ := by field_simp
-- CHECKPOINT

theorem lowENHXor_minimal_probability_bitvec (n r δ ε e : ℕ)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (hodd : (δ/2^r)%2 = 1)
    (he : 0 < e ∧ e < 2^n) (hr : r = padicValNat 2 e) (hr1 : 1 ≤ r) :
    letI : Fintype (BitVec n) := Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv
    uniformProb (fun ab : BitVec n × BitVec n =>
      lowENHXor n δ ε ab.1.toNat ab.2.toNat = e) ≤
      (2:ℚ≥0)^(r+1)/(2:ℚ≥0)^n := by
  letI : Fintype (BitVec n) := Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv
  let equiv : (Fin (2^n) × Fin (2^n)) ≃ (BitVec n × BitVec n) :=
    Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv equiv]
  simpa only [Nat.mul_div_cancel' hδ, Nat.mul_div_cancel' hε] using
    low_xor_minimal_probability n r (δ/2^r) (ε/2^r) e he hr hr1 hodd
-- CHECKPOINT

end ProvenHashes.UMASH
