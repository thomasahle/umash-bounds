import ProvenHashes.UMASHQuadraticOdd
import ProvenHashes.UMASHShortProbability

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

def quadraticValue (b c d x : ℤ) : ℤ := b*x^2+c*x+d

def quadraticSetCount (n : ℕ) (b c d : ℤ) (T : Finset ℤ) : ℕ :=
  (Finset.univ.filter (fun x : Fin (2^n) =>
    quadraticValue b c d x.val % (2:ℤ)^n ∈ T)).card

/-- The odd-linear root bound also bounds every set of outputs, without any
assumption about which bits specify that set. -/
theorem quadratic_odd_linear_set_count (n : ℕ) (b c d : ℤ) (T : Finset ℤ)
    (hc : c%2 = 1) : quadraticSetCount n b c d T ≤ 2*T.card := by
  classical
  unfold quadraticSetCount
  calc
    _ ≤ (T ×ˢ Finset.range 2).card := by
      apply Finset.card_le_card_of_injOn
        (fun x : Fin (2^n) => (quadraticValue b c d x.val % (2:ℤ)^n, x.val%2))
      · intro x hx
        exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hx).2,
          Finset.mem_range.mpr (Nat.mod_lt _ (by decide))⟩
      · intro x hx y hy hxy
        apply Fin.ext
        apply quadratic_odd_linear_parity_unique n x.val y.val b c d hc x.isLt y.isLt
          (congrArg Prod.snd hxy)
        exact congrArg Prod.fst hxy
    _ = 2*T.card := by rw [Finset.card_product, Finset.card_range]; omega
-- CHECKPOINT

def quadraticPullback (n : ℕ) (v : ℤ) (T : Finset ℤ) : Finset ℤ :=
  (Finset.Ico 0 ((2:ℤ)^n)).filter (fun z => (4*z+v) % (2:ℤ)^(n+2) ∈ T)

/-- Restricting to a fixed residue modulo four cannot create more targets. -/
theorem quadraticPullback_card_le (n : ℕ) (v : ℤ) (T : Finset ℤ) :
    (quadraticPullback n v T).card ≤ T.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun z : ℤ => (4*z+v) % (2:ℤ)^(n+2))
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · intro x hx y hy hxy
    have hx := Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1
    have hy := Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1
    have he : Int.ModEq ((2:ℤ)^(n+2)) (4*x+v) (4*y+v) := hxy
    have hm : Int.ModEq (4*(2:ℤ)^n) (4*x) (4*y) := by
      convert he.add_right_cancel' v using 1 <;> ring
    have h := Int.ModEq.mul_left_cancel' (by norm_num : (4:ℤ) ≠ 0) hm
    simpa only [Int.ModEq, Int.emod_eq_of_lt hx.1 hx.2,
      Int.emod_eq_of_lt hy.1 hy.2] using h
-- CHECKPOINT

/-- Exact compatibility of the target pullback with modular reduction. -/
theorem quadraticPullback_mem (n : ℕ) (v z : ℤ) (T : Finset ℤ) :
    z % (2:ℤ)^n ∈ quadraticPullback n v T ↔
      (4*z+v) % (2:ℤ)^(n+2) ∈ T := by
  have hpos : 0 < (2:ℤ)^n := by positivity
  have hm : Int.ModEq ((2:ℤ)^n) z (z % (2:ℤ)^n) := (Int.emod_emod _ _).symm
  have h4 : Int.ModEq ((2:ℤ)^(n+2)) (4*z+v) (4*(z % (2:ℤ)^n)+v) := by
    convert (show Int.ModEq (4*(2:ℤ)^n) (4*z) (4*(z % (2:ℤ)^n)) from
      hm.mul_left').add_right v using 1 <;> ring
  simp only [quadraticPullback, Finset.mem_filter, Finset.mem_Ico,
    Int.emod_nonneg z hpos.ne', Int.emod_lt_of_pos z hpos, and_self, true_and]
  rw [← h4]
-- CHECKPOINT

/-- One extra input bit repeats every quadratic output twice. -/
theorem quadratic_repeat_count (n : ℕ) (b c d : ℤ) (T : Finset ℤ) :
    (Finset.univ.filter (fun x : Fin (2^(n+1)) =>
      quadraticValue b c d x.val % (2:ℤ)^n ∈ T)).card =
      2*quadraticSetCount n b c d T := by
  classical
  let e : Fin 2 × Fin (2^n) ≃ Fin (2^(n+1)) :=
    finProdFinEquiv.trans (finCongr (by rw [pow_succ, Nat.mul_comm]))
  have he (u : Fin 2 × Fin (2^n)) :
      quadraticValue b c d (e u).val % (2:ℤ)^n =
        quadraticValue b c d u.2.val % (2:ℤ)^n := by
    have hx : Int.ModEq ((2:ℤ)^n) ((e u).val:ℤ) (u.2.val:ℤ) := by
      change ((u.2.val+2^n*u.1.val:ℕ):ℤ) % (2:ℤ)^n = _
      simp [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Int.add_emod]
    exact ((hx.pow 2).mul_left b |>.add (hx.mul_left c)).add_right d
  calc
    _ = ((Finset.univ : Finset (Fin 2)) ×ˢ
      Finset.univ.filter (fun x : Fin (2^n) =>
        quadraticValue b c d x.val % (2:ℤ)^n ∈ T)).card := by
      symm
      apply Finset.card_equiv e
      intro u
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, he]
    _ = _ := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]; rfl
-- CHECKPOINT

/-- Splitting an even-linear quadratic by input parity removes two output
bits. Exactly one of the two new linear coefficients is odd when b is odd. -/
theorem quadratic_parity_count (n : ℕ) (b k d : ℤ) (T : Finset ℤ) :
    quadraticSetCount (n+2) b (2*k) d T =
      2*(quadraticSetCount n b k 0 (quadraticPullback n d T) +
        quadraticSetCount n b (b+k) 0 (quadraticPullback n (b+2*k+d) T)) := by
  classical
  let e : Fin 2 × Fin (2^(n+1)) ≃ Fin (2^(n+2)) :=
    (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by
      simp only [show n+2 = (n+1)+1 by omega, pow_succ])))
  have hc : quadraticSetCount (n+2) b (2*k) d T =
      ∑ a : Fin 2, (Finset.univ.filter (fun y : Fin (2^(n+1)) =>
        quadraticValue b (2*k) d (a.val+2*y.val) % (2:ℤ)^(n+2) ∈ T)).card := by
    unfold quadraticSetCount
    rw [← Finset.card_equiv e (s := Finset.univ.filter (fun u : Fin 2 × Fin (2^(n+1)) =>
      quadraticValue b (2*k) d (u.1.val+2*u.2.val) % (2:ℤ)^(n+2) ∈ T))
      (by intro u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl)]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  have h0 (y : ℤ) : quadraticValue b (2*k) d (0+2*y) =
      4*quadraticValue b k 0 y+d := by unfold quadraticValue; ring
  have h1 (y : ℤ) : quadraticValue b (2*k) d (1+2*y) =
      4*quadraticValue b (b+k) 0 y+(b+2*k+d) := by unfold quadraticValue; ring
  rw [hc, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    h0, h1, ← quadraticPullback_mem]
  rw [quadratic_repeat_count, quadratic_repeat_count]
  omega
-- CHECKPOINT

/-- A small-set bound for every primitive quadratic modulo a power of two.
The free parameter m is the number of parity reductions; no square-root
classification or distributional assumption about T is needed. -/
theorem quadratic_set_count (m n : ℕ) (hm : 2*m ≤ n)
    (b c d : ℤ) (T : Finset ℤ) (hodd : b%2 = 1 ∨ c%2 = 1) :
    quadraticSetCount n b c d T ≤ 4*T.card*(2^m-1)+2^(n-m) := by
  induction m generalizing n b c d T with
  | zero =>
    simp only [pow_zero, Nat.sub_self, mul_zero, Nat.sub_zero, zero_add]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (Finset.card_univ.trans (Fintype.card_fin _))
  | succ m ih =>
    have hp : 1 ≤ 2^m := Nat.one_le_pow m 2 (by decide)
    have hp' : 1 ≤ 2^(m+1)-1 := by rw [pow_succ]; omega
    by_cases hc : c%2 = 1
    · have ho := quadratic_odd_linear_set_count n b c d T hc
      have hmul := Nat.mul_le_mul_left (4*T.card) hp'
      apply ho.trans
      calc
        2*T.card ≤ 4*T.card := by omega
        _ ≤ 4*T.card*(2^(m+1)-1) := by simpa only [mul_one] using hmul
        _ ≤ _ := Nat.le_add_right _ _
    · have hb : b%2 = 1 := hodd.resolve_right hc
      have hc0 : c = 2*(c/2) := by omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
      rw [Nat.add_comm 2 n] at hm ⊢
      have hmn : 2*m ≤ n := by omega
      rw [hc0, quadratic_parity_count]
      let T0 := quadraticPullback n d T
      let T1 := quadraticPullback n (b+2*(c/2)+d) T
      have hT0 : T0.card ≤ T.card := quadraticPullback_card_le _ _ _
      have hT1 : T1.card ≤ T.card := quadraticPullback_card_le _ _ _
      have hbig (c' : ℤ) (T' : Finset ℤ) (hT : T'.card ≤ T.card) :
          quadraticSetCount n b c' 0 T' ≤ 4*T.card*(2^m-1)+2^(n-m) := by
        exact (ih n hmn b c' 0 T' (Or.inl hb)).trans (by gcongr)
      have hsum : quadraticSetCount n b (c/2) 0 T0 +
          quadraticSetCount n b (b+c/2) 0 T1 ≤
            2*T.card+(4*T.card*(2^m-1)+2^(n-m)) := by
        by_cases hk : (c/2)%2 = 1
        · have hs := (quadratic_odd_linear_set_count n b (c/2) 0 T0 hk).trans
            (Nat.mul_le_mul_left 2 hT0)
          exact Nat.add_le_add hs (hbig _ T1 hT1)
        · have hk' : (b+c/2)%2 = 1 := by rw [Int.add_emod, hb]; omega
          have hs := (quadratic_odd_linear_set_count n b (b+c/2) 0 T1 hk').trans
            (Nat.mul_le_mul_left 2 hT1)
          have hl := hbig (c/2) T0 hT0
          omega
      have he : n+2-(m+1) = (n-m)+1 := by omega
      have hpow : 2^(m+1)-1 = 2*(2^m-1)+1 := by rw [pow_succ]; omega
      change 2*(quadraticSetCount n b (c/2) 0 T0 +
        quadraticSetCount n b (b+c/2) 0 T1) ≤ _
      rw [he, hpow, pow_succ]
      nlinarith
-- CHECKPOINT

/-- Output sets with at most 2^(n-h) elements have at most
4*2^(n-floor(h/2)) preimages. This is stronger than requiring selected bits. -/
theorem quadratic_small_set_count (n h : ℕ) (hh : h ≤ n)
    (b c d : ℤ) (T : Finset ℤ) (hodd : b%2 = 1 ∨ c%2 = 1)
    (hT : T.card ≤ 2^(n-h)) :
    quadraticSetCount n b c d T ≤ 4*2^(n-h/2) := by
  by_cases hs : h < 4
  · have ht : quadraticSetCount n b c d T ≤ 2^n :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (Finset.card_univ.trans (Fintype.card_fin _))
    apply ht.trans
    calc
      2^n ≤ 2^(2+(n-h/2)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 4*2^(n-h/2) := by rw [pow_add]; norm_num
  · let m := h/2-1
    have hm : 2*m ≤ n := by dsimp [m]; omega
    have hc := quadratic_set_count m n hm b c d T hodd
    have hk : h/2 ≤ n := by omega
    have hfirst : 4*2^(n-h)*2^m ≤ 2*2^(n-h/2) := by
      calc
        _ = 2^((n-h)+m+2) := by rw [pow_add, pow_add]; ring
        _ ≤ 2^((n-h/2)+1) := Nat.pow_le_pow_right (by decide) (by dsimp [m]; omega)
        _ = _ := by rw [pow_succ]; omega
    have htail : 2^(n-m) = 2*2^(n-h/2) := by
      rw [show n-m = (n-h/2)+1 by dsimp [m]; omega, pow_succ]
      omega
    calc
      _ ≤ 4*T.card*(2^m-1)+2^(n-m) := hc
      _ ≤ 4*2^(n-h)*2^m+2^(n-m) := by gcongr; exact Nat.sub_le _ _
      _ ≤ 2*2^(n-h/2)+2*2^(n-h/2) := by rw [htail]; exact Nat.add_le_add_right hfirst _
      _ = _ := by ring
-- CHECKPOINT

/-- Exact rational probability form of the small-set quadratic bound. -/
theorem quadratic_small_set_probability (n h : ℕ) (hh : h ≤ n)
    (b c d : ℤ) (T : Finset ℤ) (hodd : b%2 = 1 ∨ c%2 = 1)
    (hT : T.card ≤ 2^(n-h)) :
    uniformProb (fun x : Fin (2^n) =>
      quadraticValue b c d x.val % (2:ℤ)^n ∈ T) ≤
      min 1 ((4:ℚ≥0)/2^(h/2)) := by
  apply le_min (probability_le_one _) 
  have hc := quadratic_small_set_count n h hh b c d T hodd hT
  have hk : h/2 ≤ n := by omega
  have hp : (2:ℚ≥0)^n = 2^(n-h/2)*2^(h/2) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have he : uniformProb (fun x : Fin (2^n) =>
      quadraticValue b c d x.val % (2:ℤ)^n ∈ T) =
      (quadraticSetCount n b c d T : ℚ≥0)/(2:ℚ≥0)^n := by
    simp only [uniformProb, quadraticSetCount, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    congr 2
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he]
  calc
    (quadraticSetCount n b c d T : ℚ≥0)/(2:ℚ≥0)^n ≤
        (4*2^(n-h/2):ℚ≥0)/(2:ℚ≥0)^n := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        (Nat.cast_le.mpr hc : (quadraticSetCount n b c d T : ℚ≥0) ≤ ((4*2^(n-h/2):ℕ):ℚ≥0))
    _ = (4:ℚ≥0)/2^(h/2) := by rw [hp]; field_simp
-- CHECKPOINT

end ProvenHashes.UMASH
