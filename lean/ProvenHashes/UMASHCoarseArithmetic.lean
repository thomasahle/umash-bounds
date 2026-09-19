import ProvenHashes.UMASHPublishedArithmetic

/-! Coarse marginal constants still leave room in the published fingerprint
headline. This arithmetic consequence uses the argument from the GPT-6 Pro
handoff of 2026-09-19, Section 9, with the preserved smaller marginals.
The missing joint and message bounds remain separate propositions. -/
namespace ProvenHashes.UMASH

def coarseFingerprintRoundingK : ℚ≥0 :=
  2^83*((1:ℚ≥0)/2^87+((364816+729632:ℚ≥0)/q)*(2^19/(p-2:ℕ))+
    (2^19/(p-2:ℕ))^2)/(((q-561:ℕ):ℚ≥0)/q)

theorem fingerprint_coarse_rounding_certificate :
    coarseFingerprintRoundingK < (7:ℚ≥0)/10 ∧ (7:ℚ≥0)/10 < 1 := by
  constructor <;> apply NNRat.coe_lt_coe.mp <;>
    norm_num [coarseFingerprintRoundingK, p, q]
-- CHECKPOINT

end ProvenHashes.UMASH
