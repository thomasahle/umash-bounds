import ProvenHashes.UMASHIntegerLines

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

def wrappedProductDifferenceZ (Q δ ε A B : ℤ) : ℤ :=
  ((A+δ)%Q)*((B+ε)%Q)-A*B

def wrappedProductBranch (Q δ ε : ℤ) (z : ℤ × ℤ) : ℤ × (ℤ × ℤ) :=
  ((z.1+δ)/Q, (z.2+ε)/Q, wrappedProductDifferenceZ Q δ ε z.1 z.2/Q^2)

def wrappedProductBranches : Finset (ℤ × (ℤ × ℤ)) :=
  Finset.Ico 0 2 ×ˢ (Finset.Ico 0 2 ×ˢ Finset.Ico (-1) 1)

/-- Both products lie in the same half-open interval of length Q squared. -/
theorem wrapped_product_difference_bounds (Q δ ε A B : ℤ)
    (hQ : 0 < Q) (hA : 0 ≤ A ∧ A < Q) (hB : 0 ≤ B ∧ B < Q) :
    -Q^2 < wrappedProductDifferenceZ Q δ ε A B ∧
      wrappedProductDifferenceZ Q δ ε A B < Q^2 := by
  have hp (X Y : ℤ) (hX : 0 ≤ X ∧ X < Q) (hY : 0 ≤ Y ∧ Y < Q) :
      0 ≤ X*Y ∧ X*Y < Q^2 := by
    refine ⟨mul_nonneg hX.1 hY.1, ?_⟩
    calc
      X*Y ≤ X*Q := mul_le_mul_of_nonneg_left hY.2.le hX.1
      _ < Q*Q := mul_lt_mul_of_pos_right hX.2 hQ
      _ = Q^2 := by ring
  have hAB := hp A B hA hB
  have hAB' := hp ((A+δ)%Q) ((B+ε)%Q)
    ⟨Int.emod_nonneg _ hQ.ne', Int.emod_lt_of_pos _ hQ⟩
    ⟨Int.emod_nonneg _ hQ.ne', Int.emod_lt_of_pos _ hQ⟩
  dsimp only [wrappedProductDifferenceZ]
  constructor <;> linarith [hAB.1, hAB.2, hAB'.1, hAB'.2]
-- CHECKPOINT

/-- There are only two wraps per operand and two representatives of the
product-difference residue. This includes zero operands and negative differences. -/
theorem wrapped_product_branch_mem (Q δ ε A B : ℤ)
    (hQ : 0 < Q) (hA : 0 ≤ A ∧ A < Q) (hB : 0 ≤ B ∧ B < Q)
    (hδ : 0 ≤ δ ∧ δ < Q) (hε : 0 ≤ ε ∧ ε < Q) :
    wrappedProductBranch Q δ ε (A,B) ∈ wrappedProductBranches := by
  have hwrap (X d : ℤ) (hX : 0 ≤ X ∧ X < Q) (hd : 0 ≤ d ∧ d < Q) :
      0 ≤ (X+d)/Q ∧ (X+d)/Q < 2 := by
    refine ⟨Int.ediv_nonneg (by omega) hQ.le, ?_⟩
    apply (Int.ediv_lt_iff_lt_mul hQ).mpr
    omega
  have hdiff := wrapped_product_difference_bounds Q δ ε A B hQ hA hB
  have hQ2 : 0 < Q^2 := sq_pos_of_pos hQ
  have hrep : -1 ≤ wrappedProductDifferenceZ Q δ ε A B/Q^2 ∧
      wrappedProductDifferenceZ Q δ ε A B/Q^2 < 1 := by
    constructor
    · apply (Int.le_ediv_iff_mul_le hQ2).mpr
      nlinarith [hdiff.1]
    · apply (Int.ediv_lt_iff_lt_mul hQ2).mpr
      simpa only [one_mul] using hdiff.2
  simpa only [wrappedProductBranch, wrappedProductBranches, Finset.mem_product,
    Finset.mem_Ico] using ⟨hwrap A δ hA hδ, hwrap B ε hB hε, hrep⟩
-- CHECKPOINT

theorem wrapped_product_branches_card : wrappedProductBranches.card = 8 := by
  decide
-- CHECKPOINT

/-- On a fixed branch a prescribed product-difference residue is exactly
one integer line; the signed increments retain the actual operand wraps. -/
theorem wrapped_product_branch_line (Q δ ε A B target i j k : ℤ)
    (hbranch : wrappedProductBranch Q δ ε (A,B) = (i,j,k))
    (hres : Int.ModEq (Q^2) (wrappedProductDifferenceZ Q δ ε A B) target) :
    (δ-Q*i)*B+(ε-Q*j)*A =
      target%Q^2+Q^2*k-(δ-Q*i)*(ε-Q*j) := by
  have hi : (A+δ)/Q = i := congrArg Prod.fst hbranch
  have hj : (B+ε)/Q = j := congrArg (fun z => z.2.1) hbranch
  have hk : wrappedProductDifferenceZ Q δ ε A B/Q^2 = k :=
    congrArg (fun z => z.2.2) hbranch
  have hA := Int.emod_add_mul_ediv (A+δ) Q
  have hB := Int.emod_add_mul_ediv (B+ε) Q
  rw [hi] at hA
  rw [hj] at hB
  have hA' : (A+δ)%Q = A+(δ-Q*i) := by linarith
  have hB' : (B+ε)%Q = B+(ε-Q*j) := by linarith
  have hd := Int.emod_add_mul_ediv (wrappedProductDifferenceZ Q δ ε A B) (Q^2)
  change wrappedProductDifferenceZ Q δ ε A B%Q^2 = target%Q^2 at hres
  rw [hres, hk] at hd
  dsimp only [wrappedProductDifferenceZ] at hd
  rw [hA', hB'] at hd
  nlinarith [hd]
-- CHECKPOINT

/-- The eight-branch count used in PROOF2 Lemma 4.2. Only the nonzero
increment hypotheses are used; no valuation restriction is imposed. -/
theorem wrapped_product_residue_interval_count
    (m : ℕ) (lo hi : Fin m → ℝ) (ell : ℝ) (Q δ ε target : ℤ)
    (S : Finset (ℤ × ℤ)) (hm : 0 < m) (hell : 0 < ell) (hQ : 0 < Q)
    (hδ : 0 < δ ∧ δ < Q) (hε : 0 < ε ∧ ε < Q)
    (hbox : ∀ z ∈ S, (0 ≤ z.1 ∧ z.1 < Q) ∧ (0 ≤ z.2 ∧ z.2 < Q))
    (hres : ∀ z ∈ S, Int.ModEq (Q^2) (wrappedProductDifferenceZ Q δ ε z.1 z.2) target)
    (hlen : ∀ i, lo i ≤ hi i ∧ hi i-lo i ≤ ell)
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.Ico (lo i) (hi i)) (Set.Ico (lo j) (hi j)))
    (hcover : ∀ z ∈ S, ∃ i, lo i ≤ ((z.1*z.2:ℤ):ℝ) ∧
      ((z.1*z.2:ℤ):ℝ) < hi i) :
    (S.card:ℝ) ≤ 8*(2*Real.sqrt ((m:ℝ)*ell)+2*m) := by
  classical
  let G : (ℤ × (ℤ × ℤ)) → Finset (ℤ × ℤ) := fun k =>
    S.filter (fun z => wrappedProductBranch Q δ ε z = k)
  have hlabel (z : ℤ × ℤ) (hz : z ∈ S) :
      wrappedProductBranch Q δ ε z ∈ wrappedProductBranches :=
    wrapped_product_branch_mem Q δ ε z.1 z.2 hQ (hbox z hz).1 (hbox z hz).2
      ⟨hδ.1.le, hδ.2⟩ ⟨hε.1.le, hε.2⟩
  have hcount : S.card = ∑ k ∈ wrappedProductBranches, (G k).card :=
    Finset.card_eq_sum_card_fiberwise hlabel
  have hinc (d w : ℤ) (hd : 0 < d ∧ d < Q) (hw : 0 ≤ w ∧ w < 2) :
      d-Q*w ≠ 0 := by
    have hc : w = 0 ∨ w = 1 := by omega
    rcases hc with rfl | rfl <;> simp only [mul_zero, sub_zero, mul_one] <;> omega
  have hf (k : ℤ × (ℤ × ℤ)) (hk : k ∈ wrappedProductBranches) :
      ((G k).card:ℝ) ≤ 2*Real.sqrt ((m:ℝ)*ell)+2*m := by
    have hk' : (0 ≤ k.1 ∧ k.1 < 2) ∧ (0 ≤ k.2.1 ∧ k.2.1 < 2) ∧
        (-1 ≤ k.2.2 ∧ k.2.2 < 1) := by
      simpa only [wrappedProductBranches, Finset.mem_product, Finset.mem_Ico] using hk
    apply integer_line_product_interval_count m lo hi ell
      (δ-Q*k.1) (ε-Q*k.2.1)
      (target%Q^2+Q^2*k.2.2-(δ-Q*k.1)*(ε-Q*k.2.1)) (G k)
      hm hell (hinc δ k.1 hδ hk'.1) (hinc ε k.2.1 hε hk'.2.1)
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact wrapped_product_branch_line Q δ ε z.1 z.2 target k.1 k.2.1 k.2.2
        hz'.2 (hres z hz'.1)
    · exact hlen
    · exact hdis
    · intro z hz
      exact hcover z (Finset.mem_filter.mp hz).1
  have hcR : (S.card:ℝ) = ∑ k ∈ wrappedProductBranches, ((G k).card:ℝ) := by
    exact_mod_cast hcount
  calc
    _ = ∑ k ∈ wrappedProductBranches, ((G k).card:ℝ) := hcR
    _ ≤ ∑ _k ∈ wrappedProductBranches, (2*Real.sqrt ((m:ℝ)*ell)+2*m) :=
      Finset.sum_le_sum hf
    _ = _ := by rw [Finset.sum_const, wrapped_product_branches_card]; norm_num; ring
-- CHECKPOINT

/-- For a fixed product-difference residue, restricting the untagged high
product word to H gives the square-root count used for each XOR pattern. -/
theorem wrapped_product_high_set_count (Q δ ε target : ℤ)
    (H : Finset ℤ) (S : Finset (ℤ × ℤ)) (hQ : 0 < Q)
    (hδ : 0 < δ ∧ δ < Q) (hε : 0 < ε ∧ ε < Q)
    (hbox : ∀ z ∈ S, (0 ≤ z.1 ∧ z.1 < Q) ∧ (0 ≤ z.2 ∧ z.2 < Q))
    (hres : ∀ z ∈ S, Int.ModEq (Q^2) (wrappedProductDifferenceZ Q δ ε z.1 z.2) target)
    (hhigh : ∀ z ∈ S, z.1*z.2/Q ∈ H) :
    (S.card:ℝ) ≤ 16*(Real.sqrt ((H.card:ℝ)*(Q:ℝ))+H.card) := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨z₀, hz₀⟩ := hS
  have hH : 0 < H.card := Finset.card_pos.mpr ⟨_, hhigh z₀ hz₀⟩
  let E : {x : ℤ // x ∈ H} ≃ Fin H.card := Fintype.equivFinOfCardEq (by simp)
  let v : Fin H.card → ℤ := fun i => (E.symm i).val
  let lo : Fin H.card → ℝ := fun i => (Q:ℝ)*(v i:ℝ)
  let hi : Fin H.card → ℝ := fun i => (Q:ℝ)*((v i:ℝ)+1)
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have hlen (i : Fin H.card) : lo i ≤ hi i ∧ hi i-lo i ≤ (Q:ℝ) := by
    dsimp only [lo, hi]
    constructor <;> nlinarith
  have hdis (i j : Fin H.card) (hij : i ≠ j) :
      Disjoint (Set.Ico (lo i) (hi i)) (Set.Ico (lo j) (hi j)) := by
    have hne : v i ≠ v j := by
      intro he
      apply hij
      apply E.symm.injective
      exact Subtype.ext he
    have hord : v i+1 ≤ v j ∨ v j+1 ≤ v i := by omega
    apply Set.Ico_disjoint_Ico.mpr
    rcases hord with h | h
    · have hR : (v i:ℝ)+1 ≤ v j := by exact_mod_cast h
      exact (min_le_left _ _).trans
        ((mul_le_mul_of_nonneg_left hR hQR.le).trans (le_max_right _ _))
    · have hR : (v j:ℝ)+1 ≤ v i := by exact_mod_cast h
      exact (min_le_right _ _).trans
        ((mul_le_mul_of_nonneg_left hR hQR.le).trans (le_max_left _ _))
  have hcover (z : ℤ × ℤ) (hz : z ∈ S) :
      ∃ i, lo i ≤ ((z.1*z.2:ℤ):ℝ) ∧ ((z.1*z.2:ℤ):ℝ) < hi i := by
    let x : {x : ℤ // x ∈ H} := ⟨z.1*z.2/Q, hhigh z hz⟩
    refine ⟨E x, ?_, ?_⟩
    · have hd := Int.emod_add_mul_ediv (z.1*z.2) Q
      have hr := Int.emod_nonneg (z.1*z.2) hQ.ne'
      have hle : Q*(z.1*z.2/Q) ≤ z.1*z.2 := by linarith
      simpa only [lo, v, Equiv.symm_apply_apply, x, Int.cast_mul] using
        (show ((Q*(z.1*z.2/Q):ℤ):ℝ) ≤ ((z.1*z.2:ℤ):ℝ) by exact_mod_cast hle)
    · have hd := Int.emod_add_mul_ediv (z.1*z.2) Q
      have hr := Int.emod_lt_of_pos (z.1*z.2) hQ
      have hlt : z.1*z.2 < Q*(z.1*z.2/Q+1) := by nlinarith
      simpa only [hi, v, Equiv.symm_apply_apply, x, Int.cast_mul, Int.cast_add,
        Int.cast_one] using
        (show ((z.1*z.2:ℤ):ℝ) < ((Q*(z.1*z.2/Q+1):ℤ):ℝ) by exact_mod_cast hlt)
  have hc := wrapped_product_residue_interval_count H.card lo hi Q Q δ ε target S
    hH hQR hQ hδ hε hbox hres hlen hdis hcover
  linarith
-- CHECKPOINT

end ProvenHashes.UMASH
