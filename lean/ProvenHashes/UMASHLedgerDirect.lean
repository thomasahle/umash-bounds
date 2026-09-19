import ProvenHashes.UMASHLedgerPacked

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def ledgerNibbleDirect (x y : ℕ) : ℕ :=
  match x%16, y%16 with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 1
  | 0, 3 => 2
  | 0, 4 => 1
  | 0, 5 => 2
  | 0, 6 => 2
  | 0, 7 => 3
  | 0, 8 => 1
  | 0, 9 => 2
  | 0, 10 => 2
  | 0, 11 => 3
  | 0, 12 => 2
  | 0, 13 => 3
  | 0, 14 => 3
  | 0, 15 => 4
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 2
  | 1, 3 => 1
  | 1, 4 => 2
  | 1, 5 => 1
  | 1, 6 => 3
  | 1, 7 => 2
  | 1, 8 => 2
  | 1, 9 => 1
  | 1, 10 => 3
  | 1, 11 => 2
  | 1, 12 => 3
  | 1, 13 => 2
  | 1, 14 => 4
  | 1, 15 => 3
  | 2, 0 => 1
  | 2, 1 => 2
  | 2, 2 => 0
  | 2, 3 => 1
  | 2, 4 => 2
  | 2, 5 => 3
  | 2, 6 => 1
  | 2, 7 => 2
  | 2, 8 => 2
  | 2, 9 => 3
  | 2, 10 => 1
  | 2, 11 => 2
  | 2, 12 => 3
  | 2, 13 => 4
  | 2, 14 => 2
  | 2, 15 => 3
  | 3, 0 => 2
  | 3, 1 => 1
  | 3, 2 => 1
  | 3, 3 => 0
  | 3, 4 => 3
  | 3, 5 => 2
  | 3, 6 => 2
  | 3, 7 => 1
  | 3, 8 => 3
  | 3, 9 => 2
  | 3, 10 => 2
  | 3, 11 => 1
  | 3, 12 => 4
  | 3, 13 => 3
  | 3, 14 => 3
  | 3, 15 => 2
  | 4, 0 => 1
  | 4, 1 => 2
  | 4, 2 => 2
  | 4, 3 => 3
  | 4, 4 => 0
  | 4, 5 => 1
  | 4, 6 => 1
  | 4, 7 => 2
  | 4, 8 => 2
  | 4, 9 => 3
  | 4, 10 => 3
  | 4, 11 => 4
  | 4, 12 => 1
  | 4, 13 => 2
  | 4, 14 => 2
  | 4, 15 => 3
  | 5, 0 => 2
  | 5, 1 => 1
  | 5, 2 => 3
  | 5, 3 => 2
  | 5, 4 => 1
  | 5, 5 => 0
  | 5, 6 => 2
  | 5, 7 => 1
  | 5, 8 => 3
  | 5, 9 => 2
  | 5, 10 => 4
  | 5, 11 => 3
  | 5, 12 => 2
  | 5, 13 => 1
  | 5, 14 => 3
  | 5, 15 => 2
  | 6, 0 => 2
  | 6, 1 => 3
  | 6, 2 => 1
  | 6, 3 => 2
  | 6, 4 => 1
  | 6, 5 => 2
  | 6, 6 => 0
  | 6, 7 => 1
  | 6, 8 => 3
  | 6, 9 => 4
  | 6, 10 => 2
  | 6, 11 => 3
  | 6, 12 => 2
  | 6, 13 => 3
  | 6, 14 => 1
  | 6, 15 => 2
  | 7, 0 => 3
  | 7, 1 => 2
  | 7, 2 => 2
  | 7, 3 => 1
  | 7, 4 => 2
  | 7, 5 => 1
  | 7, 6 => 1
  | 7, 7 => 0
  | 7, 8 => 4
  | 7, 9 => 3
  | 7, 10 => 3
  | 7, 11 => 2
  | 7, 12 => 3
  | 7, 13 => 2
  | 7, 14 => 2
  | 7, 15 => 1
  | 8, 0 => 1
  | 8, 1 => 2
  | 8, 2 => 2
  | 8, 3 => 3
  | 8, 4 => 2
  | 8, 5 => 3
  | 8, 6 => 3
  | 8, 7 => 4
  | 8, 8 => 0
  | 8, 9 => 1
  | 8, 10 => 1
  | 8, 11 => 2
  | 8, 12 => 1
  | 8, 13 => 2
  | 8, 14 => 2
  | 8, 15 => 3
  | 9, 0 => 2
  | 9, 1 => 1
  | 9, 2 => 3
  | 9, 3 => 2
  | 9, 4 => 3
  | 9, 5 => 2
  | 9, 6 => 4
  | 9, 7 => 3
  | 9, 8 => 1
  | 9, 9 => 0
  | 9, 10 => 2
  | 9, 11 => 1
  | 9, 12 => 2
  | 9, 13 => 1
  | 9, 14 => 3
  | 9, 15 => 2
  | 10, 0 => 2
  | 10, 1 => 3
  | 10, 2 => 1
  | 10, 3 => 2
  | 10, 4 => 3
  | 10, 5 => 4
  | 10, 6 => 2
  | 10, 7 => 3
  | 10, 8 => 1
  | 10, 9 => 2
  | 10, 10 => 0
  | 10, 11 => 1
  | 10, 12 => 2
  | 10, 13 => 3
  | 10, 14 => 1
  | 10, 15 => 2
  | 11, 0 => 3
  | 11, 1 => 2
  | 11, 2 => 2
  | 11, 3 => 1
  | 11, 4 => 4
  | 11, 5 => 3
  | 11, 6 => 3
  | 11, 7 => 2
  | 11, 8 => 2
  | 11, 9 => 1
  | 11, 10 => 1
  | 11, 11 => 0
  | 11, 12 => 3
  | 11, 13 => 2
  | 11, 14 => 2
  | 11, 15 => 1
  | 12, 0 => 2
  | 12, 1 => 3
  | 12, 2 => 3
  | 12, 3 => 4
  | 12, 4 => 1
  | 12, 5 => 2
  | 12, 6 => 2
  | 12, 7 => 3
  | 12, 8 => 1
  | 12, 9 => 2
  | 12, 10 => 2
  | 12, 11 => 3
  | 12, 12 => 0
  | 12, 13 => 1
  | 12, 14 => 1
  | 12, 15 => 2
  | 13, 0 => 3
  | 13, 1 => 2
  | 13, 2 => 4
  | 13, 3 => 3
  | 13, 4 => 2
  | 13, 5 => 1
  | 13, 6 => 3
  | 13, 7 => 2
  | 13, 8 => 2
  | 13, 9 => 1
  | 13, 10 => 3
  | 13, 11 => 2
  | 13, 12 => 1
  | 13, 13 => 0
  | 13, 14 => 2
  | 13, 15 => 1
  | 14, 0 => 3
  | 14, 1 => 4
  | 14, 2 => 2
  | 14, 3 => 3
  | 14, 4 => 2
  | 14, 5 => 3
  | 14, 6 => 1
  | 14, 7 => 2
  | 14, 8 => 2
  | 14, 9 => 3
  | 14, 10 => 1
  | 14, 11 => 2
  | 14, 12 => 1
  | 14, 13 => 2
  | 14, 14 => 0
  | 14, 15 => 1
  | 15, 0 => 4
  | 15, 1 => 3
  | 15, 2 => 3
  | 15, 3 => 2
  | 15, 4 => 3
  | 15, 5 => 2
  | 15, 6 => 2
  | 15, 7 => 1
  | 15, 8 => 3
  | 15, 9 => 2
  | 15, 10 => 2
  | 15, 11 => 1
  | 15, 12 => 2
  | 15, 13 => 1
  | 15, 14 => 1
  | 15, 15 => 0
  | _, _ => 0


theorem ledgerNibbleDirect_certificate : ∀ x y : Fin 16,
    ledgerNibbleDirect x.val y.val = ledgerHamming 4 x.val y.val := by
  decide +kernel
-- CHECKPOINT

theorem ledgerNibbleDirect_correct (x y : ℕ) :
    ledgerNibbleDirect x y = ledgerHamming 4 x y := by
  have h := ledgerNibbleDirect_certificate
    ⟨x%16, Nat.mod_lt _ (by decide)⟩ ⟨y%16, Nat.mod_lt _ (by decide)⟩
  have hm := ledgerHamming_mod 4 x y
  norm_num only [Nat.reducePow] at hm
  calc
    _ = ledgerNibbleDirect (x%16) (y%16) := by
      unfold ledgerNibbleDirect
      rw [Nat.mod_mod, Nat.mod_mod]
    _ = ledgerHamming 4 (x%16) (y%16) := h
    _ = _ := hm
-- CHECKPOINT

def ledgerHammingDirect : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k+1, x, y => ledgerNibbleDirect x y + ledgerHammingDirect k (x/16) (y/16)

theorem ledgerHammingDirect_correct (k x y : ℕ) :
    ledgerHammingDirect k x y = ledgerHamming (4*k) x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    rw [ledgerHammingDirect, ledgerNibbleDirect_correct, ih,
      show 4*(k+1) = 4+4*k by omega, ledgerHamming_split]
    norm_num
-- CHECKPOINT

def ledgerDirectTerm (x y : LedgerDatum) : ℕ :=
  if x.2.1/2^63 = y.2.1/2^63 then
    let h := ledgerHammingDirect 16 x.1 y.2.1
    let top := if x.1/2^63%2 = y.2.1/2^63%2 then 0 else 1
    min (2^(1+h-top)) (min (276*2^(64-h)) (16*(2^((h+1)/2)+1))) * y.2.2
  else 0

theorem ledgerDirectTerm_correct (x y : LedgerDatum) :
    ledgerDirectTerm x y = ledgerFastTerm x y := by
  simp only [ledgerDirectTerm, ledgerFastTerm, ledgerFastK, ledgerHammingDirect_correct]
-- CHECKPOINT

def ledgerDirectSum (xs ys : List LedgerDatum) : ℕ :=
  (xs.map fun x => (ys.map (ledgerDirectTerm x)).sum).sum

theorem ledgerFastSum_eq_direct (xs ys : List LedgerDatum) :
    ledgerFastSum xs ys = ledgerDirectSum xs ys := by
  have ht (x : LedgerDatum) : ledgerDirectTerm x = ledgerFastTerm x :=
    funext (ledgerDirectTerm_correct x)
  simp only [ledgerFastSum, ledgerDirectSum, ht]
-- CHECKPOINT

theorem ledgerDirectSum_append (xs zs ys : List LedgerDatum) :
    ledgerDirectSum (xs ++ zs) ys = ledgerDirectSum xs ys + ledgerDirectSum zs ys := by
  simp only [ledgerDirectSum, List.map_append, List.sum_append]
-- CHECKPOINT

end ProvenHashes.UMASH
