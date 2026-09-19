import ProvenHashes.UMASHAssembly
import ProvenHashes.UMASHKeyAcceptance

namespace ProvenHashes.UMASH

/-- Corrected Lemma 8.4 has a long-message hypothesis.  In particular it makes
no claim about identities between reduced short/short constant polynomials. -/
def LongPrimaryIdentityBound : Prop := ∀ (seed : Word) (x y : Message),
  x ≠ y → (8 < x.length ∨ 8 < y.length) →
  uniformProb (fun k : DistinctOHKey =>
    comparisonPolynomial k.val seed x = comparisonPolynomial k.val seed y) ≤ weakA

def IIDLongPrimaryIdentityBound : Prop := ∀ (seed : Word) (x y : Message),
  x ≠ y → (8 < x.length ∨ 8 < y.length) →
  uniformProb (fun k : OHKey =>
    comparisonPolynomial k seed x = comparisonPolynomial k seed y) ≤ (364816:ℚ≥0)/q

def CorrectedLinear64 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
    45635 * (((L+511)/512 : ℕ) : ℚ≥0) / 2^61

def CorrectedLinear128 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤
    45635 * (((L+511)/512 : ℕ) : ℚ≥0) / 2^61

theorem short_bound_le_certifiedEnvelope (L : ℕ) :
    (1:ℚ≥0)/(q-561 : ℕ) ≤ certifiedEnvelope L := by
  by_cases h : L = 1
  · simp only [certifiedEnvelope, if_pos h, le_refl]
  · rw [certifiedEnvelope, if_neg h]
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    apply NNRat.coe_le_coe.mp
    norm_num [weakA, q]
-- CHECKPOINT

/-- The corrected assembly uses actual short/short collisions and invokes the
polynomial-identity premise only when at least one message is long. -/
theorem certified64_of_long_identity_and_short (h : LongPrimaryIdentityBound)
    (hs : ShortOneWordBound) : CertifiedAllPairs64 := by
  intro L seed x y _hL hx hy hxy
  by_cases hshort : x.length ≤ 8 ∧ y.length ≤ 8
  · exact (hs seed x y hshort.1 hshort.2 hxy).trans (short_bound_le_certifiedEnvelope L)
  · have hlong : 8 < x.length ∨ 8 < y.length := by omega
    have hL : L ≠ 1 := by intro he; subst L; simp only [mul_one] at hx hy; omega
    have hc : 1-weakA = weakComplement :=
      tsub_eq_of_eq_add (weakA_add_complement.symm.trans (add_comm _ _))
    rw [certifiedEnvelope, if_neg hL, ← hc]
    apply probability_mixture _
      (fun k : DistinctOHKey => comparisonPolynomial k.val seed x = comparisonPolynomial k.val seed y)
      (rootRate L) weakA (min_le_left _ _) (h seed x y hxy hlong)
    intro k hk
    exact comparison_slice_bound L k.val seed x y hx hy hk
-- CHECKPOINT

theorem certifiedEnvelope_le_linear (L : ℕ) (hL : 1 ≤ L) :
    certifiedEnvelope L ≤ 45635 * (((L+511)/512 : ℕ) : ℚ≥0) / 2^61 := by
  by_cases h : L = 1
  · subst L
    apply NNRat.coe_le_coe.mp
    norm_num [certifiedEnvelope, q]
  have hceil : (L+31)/32 ≤ 16*((L+511)/512) := by omega
  have hceilQ : (((L+31)/32 : ℕ) : ℚ) ≤ 16*(((L+511)/512 : ℕ) : ℚ) := by
    exact_mod_cast hceil
  have hpos : (1 : ℚ) ≤ (((L+511)/512 : ℕ) : ℚ) := by
    exact_mod_cast (show 1 ≤ (L+511)/512 by omega)
  have hr : rootRate L ≤ 2*((((L+31)/32 : ℕ) : ℚ≥0))/(p-2 : ℕ) := min_le_right _ _
  have hrQ := NNRat.coe_le_coe.mpr hr
  apply NNRat.coe_le_coe.mp
  norm_num [certifiedEnvelope, h, weakA, weakComplement, q, p] at hrQ ⊢
  nlinarith
-- CHECKPOINT

theorem correctedLinear64_of_certified (h : CertifiedAllPairs64) : CorrectedLinear64 := by
  intro L seed x y hL hx hy hxy
  exact (h L seed x y hL hx hy hxy).trans (certifiedEnvelope_le_linear L hL)
-- CHECKPOINT

theorem correctedLinear128_of_64 (h : CorrectedLinear64) : CorrectedLinear128 := by
  intro L seed x y hL hx hy hxy
  exact (fingerprint_collision_le_primary seed x y).trans (h L seed x y hL hx hy hxy)
-- CHECKPOINT

theorem corrected_joint_arithmetic :
    (4721784:ℚ≥0)/q^2 < 1/2^105 ∧
    (4721784:ℚ≥0)/(q*(q-561 : ℕ)) < 1/2^105 ∧
    (1:ℚ≥0)/2^105 < 1/2^87 := by
  constructor
  · apply NNRat.coe_lt_coe.mp; norm_num [q]
  constructor <;> apply NNRat.coe_lt_coe.mp <;> norm_num [q]
-- CHECKPOINT

end ProvenHashes.UMASH
