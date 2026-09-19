import ProvenHashes.UMASHLedgerIntegerAssembly
import ProvenHashes.UMASHMaskCensus3125

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet

/-- Prefix popcount with no finset construction during kernel evaluation. -/
def ledgerPopcount (e : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => ledgerPopcount e n + if e.testBit n then 1 else 0

theorem ledgerPopcount_correct (e n : ℕ) :
    ledgerPopcount e n = (maskBitSet n e).card := by
  induction n with
  | zero => simp [ledgerPopcount, maskBitSet]
  | succ n ih => rw [ledgerPopcount, ih, mask_bit_set_succ_card]
-- CHECKPOINT

def ledgerHighK (e : ℕ) : ℕ :=
  let h := ledgerPopcount e 64
  min (2^(1+h-(if e.testBit 63 then 1 else 0)))
    (min (276*2^(64-h)) (16*(2^((h+1)/2)+1)))

theorem ledgerHighK_correct (e : ℕ) : ledgerHighK e = highTargetKNat e := by
  simp only [ledgerHighK, ledgerPopcount_correct, highTargetKNat]
-- CHECKPOINT

/-- A checked table stores the mask, inverse image, and twisting numerator. -/
abbrev LedgerDatum := ℕ × ℕ × ℕ

def ledgerDatum (s v : ℕ) : LedgerDatum :=
  (v, (phShuffleInverse s (BitVec.ofNat 64 v)).toNat, twistHighWeightNumerator v)

def ledgerTerm (x y : LedgerDatum) : ℕ :=
  let a := BitVec.ofNat 64 x.2.1 ^^^ BitVec.ofNat 64 y.2.1
  if a.toNat < 2^63 then ledgerHighK (BitVec.ofNat 64 x.1 ^^^ a).toNat * y.2.2
  else 0

theorem ledgerTerm_correct (s u v : ℕ) :
    ledgerTerm (ledgerDatum s u) (ledgerDatum s v) =
      if (phenhPHMask s u v).toNat < 2^63 then
        highTargetKNat (phenhENHMask s u v)*twistHighWeightNumerator v else 0 := by
  simp only [ledgerTerm, ledgerDatum, BitVec.ofNat_toNat, ledgerHighK_correct,
    phenhENHMask, phenhPHMask, phShuffleInverse_xor]
  simp
-- CHECKPOINT

def ledgerSum (xs ys : List LedgerDatum) : ℕ :=
  (xs.map fun x => (ys.map (ledgerTerm x)).sum).sum

/-- The matrix can be evaluated from one certified table per shuffler. -/
theorem phenhHighLedger_eq_table (s : ℕ) :
    phenhHighLedgerNumerator s =
      ledgerSum ((sortedUnique maskList3125).map (ledgerDatum s))
        ((sortedUnique maskList3125).map (ledgerDatum s)) := by
  simp only [ledgerSum, List.map_map, Function.comp_def, ledgerTerm_correct]
  rw [phenhHighLedgerNumerator, maskSet_eq_fastCertificate]
  rfl
-- CHECKPOINT

/-- Partitioning rows preserves the exact natural-number ledger. -/
theorem ledgerSum_append (xs zs ys : List LedgerDatum) :
    ledgerSum (xs ++ zs) ys = ledgerSum xs ys + ledgerSum zs ys := by
  simp only [ledgerSum, List.map_append, List.sum_append]
-- CHECKPOINT

/-- Rewrite the table function before computing any of its entries. -/
theorem ledgerDatum_fast (s : ℕ) :
    ledgerDatum s = fun v => (v, (phShuffleInverse s (BitVec.ofNat 64 v)).toNat,
      min q ((maskPatterns v).card*(1+(highPrefixData v 64).2))) := by
  funext v
  simp only [ledgerDatum, twistHighWeightNumerator, twistHighFactorNumerator_eq_fast]
-- CHECKPOINT

/-- Checking a proposed inverse uses one forward shuffler, not 64 iterations. -/
def ledgerDatumValid (s : ℕ) (d : LedgerDatum) : Prop :=
  d.2.1 < q ∧
    (BitVec.ofNat 64 d.2.1 ^^^ phShuffleLane s (BitVec.ofNat 64 d.2.1)).toNat = d.1 ∧
    min q ((maskPatterns d.1).card*(1+(highPrefixData d.1 64).2)) = d.2.2

theorem ledgerDatum_of_valid (s : ℕ) (hs : 0 < s) (d : LedgerDatum)
    (hd : ledgerDatumValid s d) : ledgerDatum s d.1 = d := by
  rcases d with ⟨v,a,w⟩
  rcases hd with ⟨ha,hv,hw⟩
  change a < 2^64 at ha
  change min q ((maskPatterns v).card*(1+(highPrefixData v 64).2)) = w at hw
  have he := congrArg (BitVec.ofNat 64) hv.symm
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at he
  rw [ledgerDatum_fast]
  dsimp only
  rw [he, phShuffleInverse_left s hs, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, hw]
-- CHECKPOINT

/-- A table is complete when its first projection lists every mask once. -/
theorem ledgerData_of_valid (s : ℕ) (hs : 0 < s) (xs : List LedgerDatum)
    (hm : xs.map Prod.fst = sortedUnique maskList3125)
    (hv : ∀ d ∈ xs, ledgerDatumValid s d) :
    (sortedUnique maskList3125).map (ledgerDatum s) = xs := by
  rw [← hm, List.map_map]
  exact List.map_congr_left (fun d hd => ledgerDatum_of_valid s hs d (hv d hd)) |>.trans
    (List.map_id _)
-- CHECKPOINT

instance ledgerDatumValidDecidable (s : ℕ) (d : LedgerDatum) :
    Decidable (ledgerDatumValid s d) :=
  inferInstanceAs (Decidable (d.2.1 < q ∧
    (BitVec.ofNat 64 d.2.1 ^^^ phShuffleLane s (BitVec.ofNat 64 d.2.1)).toNat = d.1 ∧
    min q ((maskPatterns d.1).card*(1+(highPrefixData d.1 64).2)) = d.2.2))

theorem ledgerData_checked (s : ℕ) (hs : 0 < s) (xs : List LedgerDatum)
    (hm : xs.map Prod.fst = sortedUnique maskList3125)
    (hv : xs.all (fun d => decide (ledgerDatumValid s d)) = true) :
    (sortedUnique maskList3125).map (ledgerDatum s) = xs := by
  apply ledgerData_of_valid s hs xs hm
  intro d hd
  exact of_decide_eq_true ((List.all_eq_true.mp hv) d hd)
-- CHECKPOINT

end ProvenHashes.UMASH
