"""Generate a branch-table kernel evaluator; all 256 leaves are verified."""
from pathlib import Path

prefix = '''import ProvenHashes.UMASHLedgerPacked

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def ledgerNibbleDirect (x y : ℕ) : ℕ :=
  match x%16, y%16 with
'''
prefix += '\n'.join(f'  | {a}, {b} => {bin(a^b).count("1")}' for a in range(16) for b in range(16))
prefix += '\n  | _, _ => 0\n\n'
body = r'''
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
'''
Path('Round7LedgerDirect.stage.lean').write_text(prefix+body)
