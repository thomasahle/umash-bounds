import ProvenHashes.UMASHJointLedgerLowFinal

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet phenhENHMask phenhPHMask

/-- The separate-lane shuffler is linear over XOR at every width. -/
theorem phShuffleLane_xor {n : ℕ} (s : ℕ) (x y : BitVec n) :
    phShuffleLane s (x ^^^ y) = phShuffleLane s x ^^^ phShuffleLane s y := by
  unfold phShuffleLane
  split
  · exact BitVec.shiftLeft_xor_distrib ..
  · simp only [BitVec.shiftLeft_xor_distrib]
    ac_rfl
-- CHECKPOINT

/-- Every finite inverse iteration is linear; no positivity condition is needed. -/
theorem phShuffleInverseAux_xor {n : ℕ} (s m : ℕ) (x y : BitVec n) :
    phShuffleInverseAux s (x ^^^ y) m =
      phShuffleInverseAux s x m ^^^ phShuffleInverseAux s y m := by
  induction m with
  | zero => simp only [phShuffleInverseAux, BitVec.xor_self]; rfl
  | succ m ih =>
    simp only [phShuffleInverseAux, ih, phShuffleLane_xor]
    ac_rfl
-- CHECKPOINT

/-- Inverse values can be computed once per mask and reused for every pair. -/
theorem phShuffleInverse_xor {n : ℕ} (s : ℕ) (x y : BitVec n) :
    phShuffleInverse s (x ^^^ y) = phShuffleInverse s x ^^^ phShuffleInverse s y :=
  phShuffleInverseAux_xor s n x y
-- CHECKPOINT

def highTargetKNat (e : ℕ) : ℕ :=
  min (2^(1+(maskBitSet 64 e).card-(if e.testBit 63 then 1 else 0)))
    (min (276*2^(64-(maskBitSet 64 e).card))
      (16*(2^(((maskBitSet 64 e).card+1)/2)+1)))

/-- All high-target factors are natural numbers, despite their rational interface. -/
theorem highTargetK_eq_nat (e : ℕ) : highTargetK e = (highTargetKNat e : ℚ≥0) := by
  simp only [highTargetK, highTargetKNat, Nat.cast_min, Nat.cast_pow,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
-- CHECKPOINT

def twistHighFactorNumerator (e : ℕ) : ℕ :=
  1+∑ j ∈ Finset.range 64, 2^(j-(maskBitSet j e).card)

/-- The common denominator q eliminates every rational operation in a high weight. -/
theorem twistHighFactor_eq_numerator (e : ℕ) :
    twistHighFactor e = (twistHighFactorNumerator e : ℚ≥0)/q := by
  have hpow (j : ℕ) : (2:ℚ≥0)^j*(1/2^(maskBitSet j e).card) =
      (2:ℚ≥0)^(j-(maskBitSet j e).card) := by
    rw [mul_one_div, pow_sub₀ (2:ℚ≥0) (by norm_num : (2:ℚ≥0) ≠ 0) (mask_bit_set_card_le j e), div_eq_mul_inv]
  simp only [twistHighFactor, twistHighFactorNumerator, hpow, Nat.cast_add,
    Nat.cast_one, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat,
    add_div, Finset.sum_div]
-- CHECKPOINT

def twistHighWeightNumerator (e : ℕ) : ℕ :=
  min q ((maskPatterns e).card*twistHighFactorNumerator e)

/-- Clipping the high weight at one is exactly clipping its integer numerator at q. -/
theorem twistHighWeight_eq_numerator (e : ℕ) :
    twistHighWeight e = (twistHighWeightNumerator e : ℚ≥0)/q := by
  have hq : (q:ℚ≥0) ≠ 0 := by norm_num [q]
  simp only [twistHighWeight, twistHighFactor_eq_numerator, twistHighWeightNumerator,
    Nat.cast_min, Nat.cast_mul, ← mul_div_assoc]
  conv_lhs => lhs; rw [← div_self hq]
  exact min_div_div_right (by positivity) _ _
-- CHECKPOINT

def phenhHighLedgerNumerator (s : ℕ) : ℕ :=
  ∑ u ∈ maskSet, ∑ v ∈ maskSet,
    if (phenhPHMask s u v).toNat < 2^63 then
      highTargetKNat (phenhENHMask s u v)*twistHighWeightNumerator v else 0

/-- The exact high ledger is a natural-number sum divided by q. -/
theorem phenhHighLedger_eq_numerator (s : ℕ) :
    phenhHighLedger s = (phenhHighLedgerNumerator s : ℚ≥0)/q := by
  have hsum (T : Finset ℕ) (b : ℕ → ℕ → Bool) (g : ℕ → ℕ → ℕ) (w : ℕ → ℕ) :
      (∑ u ∈ T, ∑ v ∈ T,
        if b u v then (g u v:ℚ≥0)*((w v:ℚ≥0)/q) else 0) =
      ((∑ u ∈ T, ∑ v ∈ T, if b u v then g u v*w v else 0 : ℕ):ℚ≥0)/q := by
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    split <;> simp only [mul_div_assoc, zero_div]
  simpa only [phenhHighLedger, highTargetK_eq_nat, twistHighWeight_eq_numerator,
    phenhHighLedgerNumerator, decide_eq_true_eq] using
    hsum maskSet (fun u v => decide ((phenhPHMask s u v).toNat < 2^63))
      (fun u v => highTargetKNat (phenhENHMask s u v)) twistHighWeightNumerator
-- CHECKPOINT

def highPrefixData (e : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0,0)
  | n+1 => let z := highPrefixData e n
      (z.1+(if e.testBit n then 1 else 0), z.2+2^(n-z.1))

/-- One pass computes all prefix popcounts and their exact dyadic sum. -/
theorem highPrefixData_correct (e n : ℕ) :
    (highPrefixData e n).1 = (maskBitSet n e).card ∧
    (highPrefixData e n).2 = ∑ j ∈ Finset.range n, 2^(j-(maskBitSet j e).card) := by
  induction n with
  | zero => simp [highPrefixData, maskBitSet]
  | succ n ih =>
    simp only [highPrefixData, ih.1, ih.2, mask_bit_set_succ_card,
      Finset.sum_range_succ, and_self]
-- CHECKPOINT

/-- Computational form of the high-weight numerator using a single pass. -/
theorem twistHighFactorNumerator_eq_fast (e : ℕ) :
    twistHighFactorNumerator e = 1+(highPrefixData e 64).2 := by
  rw [(highPrefixData_correct e 64).2]
  rfl
-- CHECKPOINT

end ProvenHashes.UMASH
