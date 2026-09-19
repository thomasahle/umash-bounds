import ProvenHashes.UMASHDyadicNormalization
import ProvenHashes.UMASHRound4Obligations

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

/-- A fixed transformed coordinate and low-word mask pattern cost at most
the primitive selected-bit quadratic count, uniformly in the word width. -/
theorem low_coordinate_quadratic_fibre_count (n r e z C a b : ℕ)
    (he : 0 < e ∧ e < 2^n) (hz : z &&& e = z)
    (hr : r ≤ padicValNat 2 e) (ha : a%2 = 1)
    (hC : Int.ModEq ((2:ℤ)^n) ((2:ℤ)^r*C) ((e:ℤ)-2*z))
    (S : Finset (ℕ × ℕ)) (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hcoord : ∀ ab ∈ S, (a*ab.2+b*ab.1+2^r*a*b)%2^n = C)
    (hmask : ∀ ab ∈ S, ab.1*ab.2%2^n &&& e = z) :
    S.card ≤ 4*2^(n-(maskBitSet n e).card/2) := by
  let c : ℤ := (C:ℤ)-(2:ℤ)^r*a*b
  have hv : padicValNat 2 e < n := (dyadic_increment_padic_factor n e he).1
  have hn : ¬((2:ℤ)^n ∣ (b:ℤ) ∧ (2:ℤ)^n ∣ c) := by
    intro h
    have hh := low_coordinate_common_factor_bound n r e z n a b C he hz hr hC h.1 h.2
    omega
  obtain ⟨s, hs, b', c', hb, hc, ho⟩ := dyadic_primitive_factor n b c hn
  have hsb : (2:ℤ)^s ∣ (b:ℤ) := ⟨b', hb⟩
  have hsc : (2:ℤ)^s ∣ c := ⟨c', hc⟩
  have hsval := low_coordinate_common_factor_bound n r e z s a b C he hz hr hC hsb hsc
  have hes : 2^s ∣ e := (pow_dvd_pow 2 (by omega : s ≤ padicValNat 2 e)).trans
    pow_padicValNat_dvd
  have ho' : (-b')%2 = 1 ∨ c'%2 = 1 := by omega
  have hinj : Set.InjOn Prod.fst (↑S : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    apply Prod.ext hxy
    have hm : Nat.ModEq (2^n) (a*x.2+b*x.1+2^r*a*b) (a*y.2+b*y.1+2^r*a*b) :=
      (hcoord x hx).trans (hcoord y hy).symm
    have hm' := hm.add_right_cancel' (2^r*a*b)
    rw [hxy] at hm'
    have hm'' := hm'.add_right_cancel' (b*y.1)
    have hac : Nat.Coprime (2^n) a :=
      ((Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ha)).pow_right n).symm
    have hh := Nat.ModEq.cancel_left_of_coprime hac hm''
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hbox x hx).2,
      Nat.mod_eq_of_lt (hbox y hy).2] using hh
  rw [← Finset.card_image_of_injOn hinj]
  apply scaled_quadratic_mask_count n s e z a (-b') c' hs.le hes ha ho' (S.image Prod.fst)
  · intro A hA
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hA
    exact (hbox ab hab).1
  · intro A hA
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hA
    let Y := ab.1*ab.2%2^n
    refine ⟨Y, Nat.mod_lt _ (by positivity), hmask ab hab, ?_⟩
    have hCI : Int.ModEq ((2:ℤ)^n)
        ((a:ℤ)*ab.2+(b:ℤ)*ab.1+(2:ℤ)^r*a*b) (C:ℤ) := by
      have hh : Nat.ModEq (2^n) (a*ab.2+b*ab.1+2^r*a*b) C := by
        change _ = C%2^n
        rw [hcoord ab hab]
        exact (Nat.mod_eq_of_lt (by
          rw [← hcoord ab hab]
          exact Nat.mod_lt _ (by positivity))).symm
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        (Int.natCast_modEq_iff.mpr hh)
    have hYI : Int.ModEq ((2:ℤ)^n) ((ab.1:ℤ)*ab.2) (Y:ℤ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        (Int.natCast_modEq_iff.mpr (Nat.mod_mod (ab.1*ab.2) (2^n)).symm)
    have hquad : Int.ModEq ((2:ℤ)^n) ((a:ℤ)*((ab.1:ℤ)*ab.2))
        (-(b:ℤ)*(ab.1:ℤ)^2+c*ab.1) := by
      convert ((hCI.sub_right ((2:ℤ)^r*a*b)).mul_right (ab.1:ℤ)).add_left
        (-(b:ℤ)*(ab.1:ℤ)^2) using 1 <;> dsimp only [c] <;> ring
    have hh := (hYI.mul_left (a:ℤ)).symm.trans hquad
    convert hh using 1
    rw [hb, hc]
    ring
-- CHECKPOINT

def lowCoordinate (n r a b A B : ℕ) : ℕ := (a*B+b*A+2^r*a*b)%2^n

/-- The reduced transformed coordinate satisfies the signed-pattern
congruence imposed by the literal low-XOR event. -/
theorem low_coordinate_residue_congruence (n r a b A B e : ℕ)
    (he : lowENHXor n (2^r*a) (2^r*b) A B = e) :
    Int.ModEq ((2:ℤ)^n) ((2:ℤ)^r*lowCoordinate n r a b A B)
      ((e:ℤ)-2*(A*B%2^n &&& e:ℕ)) := by
  have hc : Int.ModEq ((2:ℤ)^n) (lowCoordinate n r a b A B:ℤ)
      ((a:ℤ)*B+(b:ℤ)*A+(2:ℤ)^r*a*b) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (Int.natCast_modEq_iff.mpr (Nat.mod_mod (a*B+b*A+2^r*a*b) (2^n)))
  exact (hc.mul_left ((2:ℤ)^r)).trans
    (low_coordinate_event_congruence n r a b A B e he)
-- CHECKPOINT

/-- For one mask pattern there are at most 2^r coordinate lifts, each
bounded by the normalized quadratic selected-bit count. -/
theorem low_xor_quadratic_pattern_count (n r a b e z : ℕ)
    (he : 0 < e ∧ e < 2^n) (hz : z &&& e = z)
    (hr : r ≤ padicValNat 2 e) (ha : a%2 = 1)
    (S : Finset (ℕ × ℕ)) (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, lowENHXor n (2^r*a) (2^r*b) ab.1 ab.2 = e)
    (hmask : ∀ ab ∈ S, ab.1*ab.2%2^n &&& e = z) :
    S.card ≤ 2^r*(4*2^(n-(maskBitSet n e).card/2)) := by
  let T := (Finset.range (2^n)).filter (fun C : ℕ =>
    Int.ModEq ((2:ℤ)^n) ((2:ℤ)^r*C) ((e:ℤ)-2*z))
  let G (C : ℕ) := S.filter (fun ab => lowCoordinate n r a b ab.1 ab.2 = C)
  have hv : padicValNat 2 e < n := (dyadic_increment_padic_factor n e he).1
  have hT : T.card ≤ 2^r := scaled_coordinate_lift_count n r ((e:ℤ)-2*z) T (by omega)
    (fun C hC => Finset.mem_range.mp (Finset.mem_filter.mp hC).1)
    (fun C hC => (Finset.mem_filter.mp hC).2)
  have hlabel (ab : ℕ × ℕ) (hab : ab ∈ S) : lowCoordinate n r a b ab.1 ab.2 ∈ T := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by positivity)), ?_⟩
    simpa only [hmask ab hab] using
      low_coordinate_residue_congruence n r a b ab.1 ab.2 e (hevent ab hab)
  have hcount : S.card = ∑ C ∈ T, (G C).card := Finset.card_eq_sum_card_fiberwise hlabel
  have hf (C : ℕ) (hC : C ∈ T) : (G C).card ≤ 4*2^(n-(maskBitSet n e).card/2) := by
    apply low_coordinate_quadratic_fibre_count n r e z C a b he hz hr ha
      (Finset.mem_filter.mp hC).2 (G C)
    · intro ab hab
      exact hbox ab (Finset.mem_filter.mp hab).1
    · intro ab hab
      exact (Finset.mem_filter.mp hab).2
    · intro ab hab
      exact hmask ab (Finset.mem_filter.mp hab).1
  calc
    S.card = ∑ C ∈ T, (G C).card := hcount
    _ ≤ ∑ _C ∈ T, 4*2^(n-(maskBitSet n e).card/2) := Finset.sum_le_sum hf
    _ = T.card*(4*2^(n-(maskBitSet n e).card/2)) := by simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hT
-- CHECKPOINT

/-- Summing all mask patterns gives the quadratic term with its exact
integer ceiling, at every width. -/
theorem low_xor_quadratic_count (n r a b e : ℕ)
    (he : 0 < e ∧ e < 2^n) (hr : r ≤ padicValNat 2 e) (ha : a%2 = 1)
    (S : Finset (ℕ × ℕ)) (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, lowENHXor n (2^r*a) (2^r*b) ab.1 ab.2 = e) :
    S.card ≤ 4*2^r*2^(((maskBitSet n e).card+1)/2)*2^n := by
  let h := (maskBitSet n e).card
  let G (z : ℕ) := S.filter (fun ab => ab.1*ab.2%2^n &&& e = z)
  have hh : h ≤ n := mask_bit_set_card_le n e
  have hlabel (ab : ℕ × ℕ) (_hab : ab ∈ S) : ab.1*ab.2%2^n &&& e ∈ submaskTargets n e := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.and_le_left.trans_lt (Nat.mod_lt _ (by positivity))), ?_⟩
    rw [Nat.and_assoc, Nat.and_self]
  have hcount : S.card = ∑ z ∈ submaskTargets n e, (G z).card :=
    Finset.card_eq_sum_card_fiberwise hlabel
  have hf (z : ℕ) (hz : z ∈ submaskTargets n e) : (G z).card ≤ 2^r*(4*2^(n-h/2)) := by
    exact low_xor_quadratic_pattern_count n r a b e z he (Finset.mem_filter.mp hz).2 hr ha
      (G z) (fun ab hab => hbox ab (Finset.mem_filter.mp hab).1)
      (fun ab hab => hevent ab (Finset.mem_filter.mp hab).1)
      (fun ab hab => (Finset.mem_filter.mp hab).2)
  calc
    S.card = ∑ z ∈ submaskTargets n e, (G z).card := hcount
    _ ≤ ∑ _z ∈ submaskTargets n e, 2^r*(4*2^(n-h/2)) := Finset.sum_le_sum hf
    _ = (submaskTargets n e).card*(2^r*(4*2^(n-h/2))) := by
      simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ 2^h*(2^r*(4*2^(n-h/2))) :=
      Nat.mul_le_mul_right _ (submask_targets_card_le n e)
    _ = 4*2^r*2^((h+1)/2)*2^n := by
      calc
        _ = (4*2^r)*(2^h*2^(n-h/2)) := by ring
        _ = (4*2^r)*2^((h+1)/2+n) := by rw [← pow_add]; congr 2; omega
        _ = _ := by rw [pow_add]; ring
-- CHECKPOINT

/-- Exact finite-uniform probability form of the width-uniform quadratic
low-target bound. The second divided increment may even be zero. -/
theorem low_xor_quadratic_probability (n r a b e : ℕ)
    (he : 0 < e ∧ e < 2^n) (hr : r ≤ padicValNat 2 e) (ha : a%2 = 1) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      lowENHXor n (2^r*a) (2^r*b) ab.1.val ab.2.val = e) ≤
      (4:ℚ≥0)*2^r*2^(((maskBitSet n e).card+1)/2)/(2:ℚ≥0)^n := by
  have hc := fin_pair_probability_of_nat_count (2^n)
    (4*2^r*2^(((maskBitSet n e).card+1)/2)*2^n)
    (fun ab => lowENHXor n (2^r*a) (2^r*b) ab.1 ab.2 = e)
    (fun S hb hE => low_xor_quadratic_count n r a b e he hr ha S hb hE)
  calc
    _ ≤ ((4:ℚ≥0)*2^r*2^(((maskBitSet n e).card+1)/2)*(2:ℚ≥0)^n)/((2:ℚ≥0)^n)^2 := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
    _ = _ := by field_simp
-- CHECKPOINT

/-- The quadratic term for the literal 64-bit word operands, in either
orientation selected by the actual minimum increment valuation. -/
theorem low_xor_quadratic_probability_word (δ ε r e : ℕ)
    (hδ : 0 < δ ∧ δ < q) (hε : 0 < ε ∧ ε < q)
    (hr : r = min (padicValNat 2 δ) (padicValNat 2 ε))
    (he : 0 < e ∧ e < q) (hd : 2^r ∣ e) :
    uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
      (4:ℚ≥0)*2^r*2^(((maskBitSet 64 e).card+1)/2)/q := by
  have hrv : r ≤ padicValNat 2 e := by
    by_contra h
    exact pow_succ_padicValNat_not_dvd (p := 2) he.1.ne'
      ((pow_dvd_pow 2 (by omega : padicValNat 2 e+1 ≤ r)).trans hd)
  have horiented (δ ε : ℕ) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (ha : (δ/2^r)%2 = 1) :
      uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
        (4:ℚ≥0)*2^r*2^(((maskBitSet 64 e).card+1)/2)/q := by
    let equiv : (Fin (2^64) × Fin (2^64)) ≃ (Word × Word) :=
      Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
    rw [← uniformProb_equiv equiv]
    have hc := low_xor_quadratic_probability 64 r (δ/2^r) (ε/2^r) e he hrv ha
    simpa only [Nat.mul_div_cancel' hδ, Nat.mul_div_cancel' hε] using hc
  obtain ⟨_,hδd,hεd,ho⟩ := minimum_increment_padic_factor 64 δ ε r hδ hε hr
  rcases ho with ho | ho
  · exact horiented δ ε hδd hεd ho
  · rw [low_xor_probability_swap]
    exact horiented ε δ hεd hδd ho
-- CHECKPOINT

/-- The first remaining obligation from goal-loop round four is closed. -/
theorem low_enh_quadratic_bound : LowENHQuadraticBound := by
  intro δ ε r e hδ₀ hδ hε₀ hε hr _hr1 he₀ he hd
  exact low_xor_quadratic_probability_word δ ε r e ⟨hδ₀,hδ⟩ ⟨hε₀,hε⟩ hr ⟨he₀,he⟩ hd
-- CHECKPOINT

/-- PROOF2 Lemma 5.2 in full, with r ≥ 1 and no stronger valuation premise. -/
theorem low_enh_target_bound : LowENHTargetBound :=
  low_enh_target_bound_of_quadratic low_enh_quadratic_bound
-- CHECKPOINT

end ProvenHashes.UMASH
