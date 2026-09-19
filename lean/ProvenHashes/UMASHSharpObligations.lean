import ProvenHashes.UMASHCorrectedObligations

namespace ProvenHashes.UMASH

/-- PROOF2 Theorem 1, including all positive ENH valuations. -/
def JointPHENHSharpBound : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → dataChecksum x = dataChecksum y →
  phDiffCount x y = 1 → enhChanges x y = 2 →
  1 ≤ enhValuation x y → enhValuation x y ≤ 63 →
  uniformProb (jointEvent seed x y) ≤ (170906186782 : ℚ≥0)/q^2

def PrimaryPHBound1123 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → 0 < phDiffCount x y →
  uniformProb (primaryEvent seed x y) ≤ (1123 : ℚ≥0)/q

def PrimaryENHOnlyBound3125 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → phDiffCount x y = 0 → lastChunk x ≠ lastChunk y →
  uniformProb (primaryEvent seed x y) ≤ (3125 : ℚ≥0)/q

def PrimaryTagOnlyBoundSharp : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → x.chunks = y.chunks → blockTag seed x ≠ blockTag seed y →
  uniformProb (primaryEvent seed x y) < (1 : ℚ≥0)/(8*q)

def PrimaryBlockBound3125 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → (x.chunks ≠ y.chunks ∨ blockTag seed x ≠ blockTag seed y) →
  uniformProb (primaryEvent seed x y) ≤ (3125 : ℚ≥0)/q

def IIDLongPrimaryIdentityBound3125 : Prop := ∀ (seed : Word) (x y : Message),
  x ≠ y → (8 < x.length ∨ 8 < y.length) →
  uniformProb (fun k : OHKey =>
    comparisonPolynomial k seed x = comparisonPolynomial k seed y) ≤ (3125 : ℚ≥0)/q

def LongPrimaryIdentityBound3125 : Prop := ∀ (seed : Word) (x y : Message),
  x ≠ y → (8 < x.length ∨ 8 < y.length) →
  uniformProb (fun k : DistinctOHKey =>
    comparisonPolynomial k.val seed x = comparisonPolynomial k.val seed y) ≤ sharpA

def CertifiedAllPairs64_3125 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤ certifiedEnvelope3125 L

def CertifiedAllPairs128_3125 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤ certifiedEnvelope3125 L

def CorrectedLinear64_423 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
    423 * (((L+511)/512 : ℕ) : ℚ≥0) / 2^61

def CorrectedLinear128_423 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤
    423 * (((L+511)/512 : ℕ) : ℚ≥0) / 2^61

/-- Only a logical interface; the premise is separately recorded as an obligation. -/
theorem openPHENH_of_sharp_joint (h : JointPHENHSharpBound) : OpenPHENH := by
  intro seed x y hx hy hc hsum hp he hr
  have hlo : 1 ≤ enhValuation x y := by omega
  have hhi : enhValuation x y ≤ 63 := by omega
  exact (h seed x y hx hy hc hsum hp he hlo hhi).trans_lt
    (phenh_sharp_arithmetic.1.trans phenh_sharp_arithmetic.2.2)
-- CHECKPOINT

/-- Distinct-key transfer preserves the strict 90-bit joint conclusion. -/
theorem phenh_distinct_of_sharp_joint (h : JointPHENHSharpBound)
    (seed : Word) (x y : Block) (hx : x.Valid) (hy : y.Valid)
    (hc : sameCount x y) (hsum : dataChecksum x = dataChecksum y)
    (hp : phDiffCount x y = 1) (he : enhChanges x y = 2)
    (hr : 1 ≤ enhValuation x y) (hr' : enhValuation x y ≤ 63) :
    uniformProb (fun k : DistinctOHKey => jointEvent seed x y k.val) < (1 : ℚ≥0)/2^90 := by
  have hh := distinct_probability_le (jointEvent seed x y) ((170906186782 : ℚ≥0)/q)
    (by simpa only [div_div, pow_two] using h seed x y hx hy hc hsum hp he hr hr')
  apply hh.trans_lt
  simpa only [div_div, Nat.cast_mul] using phenh_sharp_arithmetic.2.1
-- CHECKPOINT

end ProvenHashes.UMASH
