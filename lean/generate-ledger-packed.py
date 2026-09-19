"""Emit a tiny untrusted four-bit distance table and its kernel certificates."""
from pathlib import Path

table = sum(bin(a ^ b).count('1') << (3*(16*a+b)) for a in range(16) for b in range(16))
path = Path('Round7LedgerPacked.stage.lean')
prefix = path.read_text().split('\ndef ledgerNibbleDistance')[0].split('\nend ProvenHashes.UMASH')[0]
body = r'''
def ledgerNibbleDistance (x y : ℕ) : ℕ :=
  NIBBLE_TABLE / 8^(16*(x%16)+y%16) % 8

/-- All 256 four-bit distances, checked with ordinary kernel reduction. -/
theorem ledgerNibbleDistance_certificate : ∀ x y : Fin 16,
    ledgerNibbleDistance x.val y.val = ledgerHamming 4 x.val y.val := by
  decide +kernel
-- CHECKPOINT

theorem ledgerNibbleDistance_correct (x y : ℕ) :
    ledgerNibbleDistance x y = ledgerHamming 4 x y := by
  have h := ledgerNibbleDistance_certificate
    ⟨x%16, Nat.mod_lt _ (by decide)⟩ ⟨y%16, Nat.mod_lt _ (by decide)⟩
  have hm := ledgerHamming_mod 4 x y
  norm_num only [Nat.reducePow] at hm
  calc
    _ = ledgerNibbleDistance (x%16) (y%16) := by
      simp only [ledgerNibbleDistance, Nat.mod_mod]
    _ = ledgerHamming 4 (x%16) (y%16) := h
    _ = _ := hm
-- CHECKPOINT

def ledgerNibbleHamming : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k+1, x, y => ledgerNibbleDistance x y + ledgerNibbleHamming k (x/16) (y/16)

theorem ledgerNibbleHamming_correct (k x y : ℕ) :
    ledgerNibbleHamming k x y = ledgerHamming (4*k) x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    rw [ledgerNibbleHamming, ledgerNibbleDistance_correct, ih,
      show 4*(k+1) = 4+4*k by omega, ledgerHamming_split]
    norm_num
-- CHECKPOINT

def ledgerPackedTerm (x y : LedgerDatum) : ℕ :=
  if x.2.1/2^63 = y.2.1/2^63 then
    let h := ledgerNibbleHamming 16 x.1 y.2.1
    let top := if x.1/2^63%2 = y.2.1/2^63%2 then 0 else 1
    min (2^(1+h-top)) (min (276*2^(64-h)) (16*(2^((h+1)/2)+1))) * y.2.2
  else 0

theorem ledgerPackedTerm_correct (x y : LedgerDatum) :
    ledgerPackedTerm x y = ledgerFastTerm x y := by
  simp only [ledgerPackedTerm, ledgerFastTerm, ledgerFastK, ledgerNibbleHamming_correct]
-- CHECKPOINT

def ledgerPackedSum (xs ys : List LedgerDatum) : ℕ :=
  (xs.map fun x => (ys.map (ledgerPackedTerm x)).sum).sum

theorem ledgerFastSum_eq_packed (xs ys : List LedgerDatum) :
    ledgerFastSum xs ys = ledgerPackedSum xs ys := by
  have ht (x : LedgerDatum) : ledgerPackedTerm x = ledgerFastTerm x :=
    funext (ledgerPackedTerm_correct x)
  simp only [ledgerFastSum, ledgerPackedSum, ht]
-- CHECKPOINT

theorem ledgerPackedSum_append (xs zs ys : List LedgerDatum) :
    ledgerPackedSum (xs ++ zs) ys = ledgerPackedSum xs ys + ledgerPackedSum zs ys := by
  simp only [ledgerPackedSum, List.map_append, List.sum_append]
-- CHECKPOINT

end ProvenHashes.UMASH
'''
path.write_text(prefix.rstrip() + '\n\n' + body.replace('NIBBLE_TABLE', str(table)))
