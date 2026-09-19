import ProvenHashes.UMASHLedgerTables

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Strip the bottom bit before counting the remaining prefix. -/
theorem ledgerPopcount_shift (e n : ℕ) :
    ledgerPopcount e (n+1) = ledgerPopcount (e/2) n + if e.testBit 0 then 1 else 0 := by
  induction n with
  | zero => simp [ledgerPopcount]
  | succ n ih =>
    rw [ledgerPopcount, ih, ledgerPopcount, Nat.testBit_succ]
    omega
-- CHECKPOINT

/-- Direct Hamming distance avoids repeated recursive shifts and XOR construction. -/
def ledgerHamming : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, x, y => ledgerHamming n (x/2) (y/2) +
      if Bool.xor (decide (x%2 = 1)) (decide (y%2 = 1)) then 1 else 0

theorem ledgerHamming_correct (n x y : ℕ) :
    ledgerHamming n x y = ledgerPopcount (x ^^^ y) n := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    have hdiv : (x ^^^ y)/2 = x/2 ^^^ y/2 := @Nat.xor_div_two_pow x y 1
    rw [ledgerHamming, ih, ledgerPopcount_shift, hdiv, Nat.testBit_xor,
      Nat.testBit_zero, Nat.testBit_zero]
-- CHECKPOINT

def ledgerPrepare (d : LedgerDatum) : LedgerDatum :=
  ((BitVec.ofNat 64 d.1 ^^^ BitVec.ofNat 64 d.2.1).toNat,
    (BitVec.ofNat 64 d.2.1).toNat, d.2.2)

def ledgerFastK (x y : ℕ) : ℕ :=
  let h := ledgerHamming 64 x y
  let top := if x/2^63%2 = y/2^63%2 then 0 else 1
  min (2^(1+h-top)) (min (276*2^(64-h)) (16*(2^((h+1)/2)+1)))

theorem ledgerFastK_correct (x y : ℕ) :
    ledgerFastK x y = ledgerHighK (x ^^^ y) := by
  simp only [ledgerFastK, ledgerHamming_correct, ledgerHighK]
  rw [Nat.testBit_xor]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  have hx := Nat.mod_lt (x/2^63) (by decide : 0 < 2)
  have hy := Nat.mod_lt (y/2^63) (by decide : 0 < 2)
  have he : (if x/2^63%2 = y/2^63%2 then 0 else 1) =
      (if Bool.xor (decide (x/2^63%2 = 1)) (decide (y/2^63%2 = 1)) then 1 else 0) := by
    interval_cases hxv : x/2^63%2 <;> interval_cases hyv : y/2^63%2 <;> decide
  rw [he]
-- CHECKPOINT

def ledgerFastTerm (x y : LedgerDatum) : ℕ :=
  if x.2.1/2^63 = y.2.1/2^63 then ledgerFastK x.1 y.2.1 * y.2.2 else 0

theorem ledgerTerm_eq_fast (x y : LedgerDatum) :
    ledgerTerm x y = ledgerFastTerm (ledgerPrepare x) (ledgerPrepare y) := by
  let a := BitVec.ofNat 64 x.2.1
  let b := BitVec.ofNat 64 y.2.1
  let u := BitVec.ofNat 64 x.1
  have htop : (a ^^^ b).toNat < 2^63 ↔ a.toNat/2^63 = b.toNat/2^63 := by
    have hh : (a.toNat ^^^ b.toNat)/2^63 = 0 ↔ a.toNat/2^63 = b.toNat/2^63 := by
      rw [Nat.xor_div_two_pow, Nat.xor_eq_zero]
    simpa only [BitVec.toNat_xor, Nat.div_eq_zero_iff,
      (by norm_num : (2:ℕ)^63 ≠ 0), false_or] using hh
  have he : (u ^^^ (a ^^^ b)).toNat = (u ^^^ a).toNat ^^^ b.toNat := by
    rw [← BitVec.xor_assoc, BitVec.toNat_xor]
  change (if (a ^^^ b).toNat < 2^63 then ledgerHighK (u ^^^ (a ^^^ b)).toNat*y.2.2 else 0) = _
  simp only [ledgerFastTerm, ledgerPrepare, ledgerFastK_correct]
  simp only [htop, he]
  rfl
-- CHECKPOINT

def ledgerFastSum (xs ys : List LedgerDatum) : ℕ :=
  (xs.map fun x => (ys.map (ledgerFastTerm x)).sum).sum

theorem ledgerSum_eq_fast (xs ys : List LedgerDatum) :
    ledgerSum xs ys = ledgerFastSum (xs.map ledgerPrepare) (ys.map ledgerPrepare) := by
  have ht (x : LedgerDatum) : ledgerTerm x = fun y =>
      ledgerFastTerm (ledgerPrepare x) (ledgerPrepare y) := funext (ledgerTerm_eq_fast x)
  simp only [ledgerSum, ledgerFastSum, List.map_map, Function.comp_def, ht]
-- CHECKPOINT

theorem ledgerFastSum_append (xs zs ys : List LedgerDatum) :
    ledgerFastSum (xs ++ zs) ys = ledgerFastSum xs ys + ledgerFastSum zs ys := by
  simp only [ledgerFastSum, List.map_append, List.sum_append]
-- CHECKPOINT

end ProvenHashes.UMASH
