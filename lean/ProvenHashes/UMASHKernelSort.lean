import ProvenHashes.UMASHENHCount
import Mathlib.Data.List.Destutter
import Mathlib.Data.List.Sort

namespace ProvenHashes.UMASH

def kernelMerge {α : Type*} [LinearOrder α] : ℕ → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, x::xs, y::ys =>
    if x ≤ y then x :: kernelMerge n xs (y::ys)
    else y :: kernelMerge n (x::xs) ys

theorem kernelMerge_eq {α : Type*} [LinearOrder α] (n : ℕ) (xs ys : List α)
    (h : xs.length+ys.length ≤ n) :
    kernelMerge n xs ys = xs.merge ys (· ≤ ·) := by
  induction n generalizing xs ys with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hx,hy,kernelMerge]
  | succ n ih =>
    cases xs with
    | nil => simp [kernelMerge]
    | cons x xs =>
      cases ys with
      | nil => simp [kernelMerge]
      | cons y ys =>
        simp only [kernelMerge, List.merge, decide_eq_true_eq]
        split_ifs <;> congr 1 <;> apply ih <;> simp only [List.length_cons] at h ⊢ <;> omega
-- CHECKPOINT

def kernelSort {α : Type*} [LinearOrder α] : ℕ → List α → List α
  | 0, xs => xs
  | _+1, [] => []
  | _+1, [a] => [a]
  | n+1, a::b::xs =>
    let lr := List.MergeSort.Internal.splitInTwo ⟨a::b::xs, rfl⟩
    kernelMerge (a::b::xs).length (kernelSort n lr.1.val) (kernelSort n lr.2.val)

theorem kernelSort_eq {α : Type*} [LinearOrder α] (n : ℕ) (xs : List α)
    (h : xs.length ≤ n) : kernelSort n xs = xs.mergeSort (· ≤ ·) := by
  induction n generalizing xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hx,kernelSort,List.mergeSort]
  | succ n ih =>
    cases xs with
    | nil => simp [kernelSort,List.mergeSort]
    | cons a xs =>
      cases xs with
      | nil => simp [kernelSort,List.mergeSort]
      | cons b xs =>
        let lr := List.MergeSort.Internal.splitInTwo ⟨a::b::xs, rfl⟩
        have hl : lr.1.val.length ≤ n := by
          have hh := lr.1.property
          simp only [List.length_cons] at h hh
          omega
        have hr : lr.2.val.length ≤ n := by
          have hh := lr.2.property
          simp only [List.length_cons] at h hh
          omega
        rw [kernelSort, List.mergeSort]
        change kernelMerge (a::b::xs).length (kernelSort n lr.1.val) (kernelSort n lr.2.val) = _
        rw [ih lr.1.val hl, ih lr.2.val hr]
        apply kernelMerge_eq
        rw [(List.mergeSort_perm lr.1.val (· ≤ ·)).length_eq,
          (List.mergeSort_perm lr.2.val (· ≤ ·)).length_eq]
        have hl := lr.1.property
        have hr := lr.2.property
        omega
-- CHECKPOINT

end ProvenHashes.UMASH
