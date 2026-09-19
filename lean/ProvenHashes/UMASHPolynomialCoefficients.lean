import ProvenHashes.UMASHPolynomial
import Mathlib.Data.List.GetD

namespace ProvenHashes.UMASH
open Polynomial
set_option maxHeartbeats 2000000

noncomputable def fieldCoefficients (xs : List Chunk) : List Field :=
  xs.flatMap (fun x => [(project x).1, (project x).2])

theorem fieldCoefficients_length (xs : List Chunk) : (fieldCoefficients xs).length = 2*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [fieldCoefficients, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at *
    omega
-- CHECKPOINT

theorem coeffs_coeff_getD (as : List Field) (n : ℕ) :
    (Classic.coeffs as).coeff n = as.getD n 0 := by
  induction as generalizing n with
  | nil => simp [Classic.coeffs]
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ n => simp [Classic.coeffs, Polynomial.coeff_add, ih]
-- CHECKPOINT

theorem blockPolynomial_coeff_succ (xs : List Chunk) (n : ℕ) :
    (blockPolynomial xs).coeff (n+1) = (fieldCoefficients xs).reverse.getD n 0 := by
  rw [blockPolynomial, Classic.positive, Polynomial.coeff_X_mul, coeffs_coeff_getD]
  rfl
-- CHECKPOINT

theorem blockPolynomial_cons_top (x : Chunk) (xs : List Chunk) :
    (blockPolynomial (x::xs)).coeff (2*xs.length+2) = (project x).1 ∧
    (blockPolynomial (x::xs)).coeff (2*xs.length+1) = (project x).2 := by
  have hlen : (fieldCoefficients (x::xs)).length = 2*xs.length+2 := by
    rw [fieldCoefficients_length, List.length_cons]
    omega
  constructor
  · rw [show 2*xs.length+2 = (2*xs.length+1)+1 by omega, blockPolynomial_coeff_succ,
      List.getD_reverse _ (by rw [hlen]; omega), hlen,
      show 2*xs.length+2-1-(2*xs.length+1) = 0 by omega]
    rfl
  · rw [blockPolynomial_coeff_succ, List.getD_reverse _ (by rw [hlen]; omega), hlen,
      show 2*xs.length+2-1-2*xs.length = 1 by omega]
    rfl
-- CHECKPOINT

theorem fieldCoefficients_injective (xs ys : List Chunk)
    (he : fieldCoefficients xs = fieldCoefficients ys) : xs.map project = ys.map project := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp [fieldCoefficients] at he
  | cons x xs ih =>
    cases ys with
    | nil => simp [fieldCoefficients] at he
    | cons y ys =>
      simp only [fieldCoefficients, List.flatMap_cons, List.cons_append, List.nil_append,
        List.cons.injEq] at he
      have hxy : project x = project y := Prod.ext he.1 he.2.1
      simpa only [List.map_cons, hxy] using congrArg (List.cons (project y)) (ih ys he.2.2)
-- CHECKPOINT

theorem blockPolynomial_same_length (xs ys : List Chunk) (hl : xs.length = ys.length)
    (he : blockPolynomial xs = blockPolynomial ys) : xs.map project = ys.map project := by
  change Classic.positive (fieldCoefficients xs).reverse =
    Classic.positive (fieldCoefficients ys).reverse at he
  have hf := Classic.coeffs_inj_length
    (by simp only [List.length_reverse, fieldCoefficients_length, hl])
    (Classic.positive_injective he)
  exact fieldCoefficients_injective xs ys (List.reverse_inj.mp hf)
-- CHECKPOINT

theorem blockPolynomial_head_zero_of_shorter (x : Chunk) (xs ys : List Chunk)
    (hl : ys.length < (x::xs).length) (he : blockPolynomial (x::xs) = blockPolynomial ys) :
    project x = (0,0) := by
  have hd := blockPolynomial_degree ys
  have h1 := congrArg (fun P : Polynomial Field => P.coeff (2*xs.length+2)) he
  have h2 := congrArg (fun P : Polynomial Field => P.coeff (2*xs.length+1)) he
  dsimp only at h1 h2
  rw [(blockPolynomial_cons_top x xs).1,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by simp only [List.length_cons] at hl; omega)] at h1
  rw [(blockPolynomial_cons_top x xs).2,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by simp only [List.length_cons] at hl; omega)] at h2
  exact Prod.ext h1 h2
-- CHECKPOINT

end ProvenHashes.UMASH
