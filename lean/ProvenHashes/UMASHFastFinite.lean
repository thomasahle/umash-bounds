import ProvenHashes.UMASHKernelSort
import Mathlib.Data.List.Destutter
import Mathlib.Data.List.Sort

namespace ProvenHashes.UMASH

/-- Kernel-computable distinct values, using sorting followed by one linear pass. -/
def sortedUnique {α : Type*} [LinearOrder α] (xs : List α) : List α :=
  (kernelSort xs.length xs).destutter (· ≠ ·)

theorem sortedUnique_eq_dedup {α : Type*} [LinearOrder α] (xs : List α) :
    sortedUnique xs = (xs.mergeSort (· ≤ ·)).dedup := by
  unfold sortedUnique
  rw [kernelSort_eq xs.length xs le_rfl]
  exact (List.sorted_mergeSort' (· ≤ ·) xs).destutter_eq_dedup
-- CHECKPOINT

theorem sortedUnique_nodup {α : Type*} [LinearOrder α] (xs : List α) :
    (sortedUnique xs).Nodup := by
  rw [sortedUnique_eq_dedup]
  exact List.nodup_dedup _
-- CHECKPOINT

theorem sortedUnique_toFinset {α : Type*} [LinearOrder α] (xs : List α) :
    (sortedUnique xs).toFinset = xs.toFinset := by
  rw [sortedUnique_eq_dedup]
  calc
    _ = (xs.mergeSort (· ≤ ·)).toFinset := by ext a; simp
    _ = xs.toFinset := List.toFinset_eq_of_perm _ _ (List.mergeSort_perm xs (· ≤ ·))
-- CHECKPOINT

/-- This finset retains the sorted list as data; no quadratic deduplication
is evaluated when a later certificate asks for its cardinality. -/
def fastFinset {α : Type*} [LinearOrder α] (xs : List α) : Finset α :=
  ⟨sortedUnique xs, sortedUnique_nodup xs⟩

theorem fastFinset_eq {α : Type*} [LinearOrder α] (xs : List α) :
    fastFinset xs = xs.toFinset := by
  exact (List.toFinset_eq (sortedUnique_nodup xs)).trans (sortedUnique_toFinset xs)
-- CHECKPOINT

theorem toFinset_card_sortedUnique {α : Type*} [LinearOrder α] (xs : List α) :
    xs.toFinset.card = (sortedUnique xs).length := by
  rw [← fastFinset_eq]
  rfl
-- CHECKPOINT

end ProvenHashes.UMASH
