import ProvenHashes.UMASHModel

/-! Exact arithmetic for the bounds in the supplied lane files. These theorems
certify the constants, not the probabilistic premises of those files. -/
namespace ProvenHashes.UMASH

/-- Corrected block constant from the even-PH case, 604 squared.
The historical name is retained for source compatibility only. -/
def weakA : ℚ≥0 := (364816 : ℚ≥0) / (q-561 : ℕ)
def weakComplement : ℚ≥0 := ((q-561-364816 : ℕ) : ℚ≥0) / (q-561 : ℕ)
def rootRate (L : ℕ) : ℚ≥0 := min 1 (2 * (((L+31)/32 : ℕ) : ℚ≥0) / (p-2 : ℕ))
def certifiedEnvelope (L : ℕ) : ℚ≥0 :=
  if L = 1 then (1 : ℚ≥0) / (q-561 : ℕ) else weakA + weakComplement*rootRate L
def certifiedSlope : ℚ≥0 :=
  420622658368725195035431 / 42535295865117306584003665538960066195

theorem certifiedEnvelope_two : certifiedEnvelope 2 = 2*certifiedSlope := by
  apply NNRat.coe_inj.mp
  norm_num [certifiedEnvelope, weakA, weakComplement, rootRate, certifiedSlope, p, q, NNRat.coe_min]
-- CHECKPOINT

/-- An exact rational way to state that the score exceeds 25.6 bits:
the fifth power of the rate per word is below 2^-128. -/
theorem certifiedSlope_better_than_25_6 : certifiedSlope^5 < 1/(2:ℚ≥0)^128 := by
  apply NNRat.coe_lt_coe.mp
  norm_num [certifiedSlope]
-- CHECKPOINT

theorem mask_square : (852 : ℕ)^2 = 725904 := by norm_num
-- CHECKPOINT

theorem subcase_b_constant : (345763417 : ℚ≥0)/2^116 < 1/2^87 := by
  apply NNRat.coe_lt_coe.mp; norm_num
-- CHECKPOINT

theorem one_word_enh_constant : (852*32042 : ℚ≥0)/2^128 < 1/2^103 := by
  apply NNRat.coe_lt_coe.mp; norm_num
-- CHECKPOINT

theorem ph_enh_constant : (111924178297 : ℚ≥0)/2^128 < 1/2^91 := by
  apply NNRat.coe_lt_coe.mp; norm_num
-- CHECKPOINT

theorem tag_only_constant : (11946240 : ℚ≥0)/2^116 < 1/2^92 := by
  apply NNRat.coe_lt_coe.mp; norm_num
-- CHECKPOINT

theorem different_counts_constant : (81 : ℚ≥0)*(2*q-1 : ℕ)/(q:ℚ≥0)^2 < 162/q := by
  apply NNRat.coe_lt_coe.mp
  norm_num [q]
-- CHECKPOINT

theorem checksum_weight_constant : (101 : ℚ≥0)/2 + 909712/q < 51 := by
  apply NNRat.coe_lt_coe.mp
  norm_num [q]
-- CHECKPOINT

theorem weak_noPH_rounding :
    (13250910204502170674351448317121 : ℚ≥0)/2^128 ≤ 718333281557/q := by
  apply NNRat.coe_le_coe.mp
  norm_num [q]
-- CHECKPOINT

theorem weak_PH_rounding :
    (11989226195148851570875316890129934569436235759441 : ℚ≥0) /
      392318858461667547739736838950479151006397215279002157056 ≤ 563730706526/q := by
  apply NNRat.coe_le_coe.mp
  norm_num [q]
-- CHECKPOINT

theorem weakA_add_complement : weakA + weakComplement = 1 := by
  apply NNRat.coe_inj.mp
  norm_num [weakA, weakComplement, q]
-- CHECKPOINT

theorem certifiedEnvelope_per_word (L : ℕ) (hL : 1 ≤ L) :
    certifiedEnvelope L ≤ (L : ℚ≥0)*certifiedSlope := by
  by_cases h : L = 1
  · subst L
    apply NNRat.coe_le_coe.mp
    norm_num [certifiedEnvelope, certifiedSlope, q]
  have htwo : 2 ≤ L := by omega
  have hceilNat : 2*((L+31)/32) ≤ L := by omega
  have hceil : 2*((((L+31)/32 : ℕ) : ℚ)) ≤ (L : ℚ) := by exact_mod_cast hceilNat
  have htwoQ : (2 : ℚ) ≤ L := by exact_mod_cast htwo
  have hr : rootRate L ≤ 2 * (((L+31)/32 : ℕ) : ℚ≥0)/(p-2 : ℕ) := min_le_right _ _
  have hrQ := NNRat.coe_le_coe.mpr hr
  norm_num [p] at hrQ
  apply NNRat.coe_le_coe.mp
  norm_num [certifiedEnvelope, h, weakA, weakComplement, certifiedSlope, q]
  nlinarith
-- CHECKPOINT

/-- PROOF3's distinct-key block rate. The 364816 constant remains unchanged. -/
def sharpA : ℚ≥0 := (3125 : ℚ≥0) / (q-561 : ℕ)
def sharpComplement : ℚ≥0 := ((q-561-3125 : ℕ) : ℚ≥0) / (q-561 : ℕ)
def certifiedEnvelope3125 (L : ℕ) : ℚ≥0 :=
  if L = 1 then (1 : ℚ≥0) / (q-561 : ℕ) else sharpA + sharpComplement*rootRate L
def certifiedSlope3125 : ℚ≥0 :=
  1448530578388042537297 / 17014118346046922633601466215584026478

theorem sharpA_add_complement : sharpA + sharpComplement = 1 := by
  apply NNRat.coe_inj.mp
  norm_num [sharpA, sharpComplement, q]
-- CHECKPOINT

theorem certifiedEnvelope3125_two : certifiedEnvelope3125 2 = 2*certifiedSlope3125 := by
  apply NNRat.coe_inj.mp
  norm_num [certifiedEnvelope3125, sharpA, sharpComplement, rootRate,
    certifiedSlope3125, p, q, NNRat.coe_min]
-- CHECKPOINT

theorem certified3125_linear_certificate :
    (422 : ℚ≥0) < 2^61*(sharpA+32/(p-2 : ℕ)) ∧
    2^61*(sharpA+32/(p-2 : ℕ)) < (423 : ℚ≥0) := by
  constructor <;> apply NNRat.coe_lt_coe.mp <;> norm_num [sharpA, p, q]
-- CHECKPOINT

set_option exponentiation.threshold 8192 in
theorem certifiedSlope3125_score_lower :
    certifiedSlope3125^50 < (1 : ℚ≥0)/2^2669 := by
  apply NNRat.coe_lt_coe.mp
  norm_num [certifiedSlope3125]
-- CHECKPOINT

set_option exponentiation.threshold 8192 in
theorem certifiedSlope3125_score_upper :
    (1 : ℚ≥0)/2^5339 < certifiedSlope3125^100 := by
  apply NNRat.coe_lt_coe.mp
  norm_num [certifiedSlope3125]
-- CHECKPOINT

theorem certifiedEnvelope3125_per_word (L : ℕ) (hL : 1 ≤ L) :
    certifiedEnvelope3125 L ≤ (L : ℚ≥0)*certifiedSlope3125 := by
  by_cases h : L = 1
  · subst L
    apply NNRat.coe_le_coe.mp
    norm_num [certifiedEnvelope3125, certifiedSlope3125, q]
  have htwo : 2 ≤ L := by omega
  have hceilNat : 2*((L+31)/32) ≤ L := by omega
  have hceil : 2*((((L+31)/32 : ℕ) : ℚ)) ≤ (L : ℚ) := by exact_mod_cast hceilNat
  have htwoQ : (2 : ℚ) ≤ L := by exact_mod_cast htwo
  have hr : rootRate L ≤ 2 * (((L+31)/32 : ℕ) : ℚ≥0)/(p-2 : ℕ) := min_le_right _ _
  have hrQ := NNRat.coe_le_coe.mpr hr
  norm_num [p] at hrQ
  apply NNRat.coe_le_coe.mp
  norm_num [certifiedEnvelope3125, h, sharpA, sharpComplement, certifiedSlope3125, q]
  nlinarith
-- CHECKPOINT

theorem certifiedEnvelope3125_le_linear (L : ℕ) (hL : 1 ≤ L) :
    certifiedEnvelope3125 L ≤ 423 * (((L+511)/512 : ℕ) : ℚ≥0) / 2^61 := by
  by_cases h : L = 1
  · subst L
    apply NNRat.coe_le_coe.mp
    norm_num [certifiedEnvelope3125, q]
  have hceil : (L+31)/32 ≤ 16*((L+511)/512) := by omega
  have hceilQ : (((L+31)/32 : ℕ) : ℚ) ≤ 16*(((L+511)/512 : ℕ) : ℚ) := by
    exact_mod_cast hceil
  have hpos : (1 : ℚ) ≤ (((L+511)/512 : ℕ) : ℚ) := by
    exact_mod_cast (show 1 ≤ (L+511)/512 by omega)
  have hr : rootRate L ≤ 2*((((L+31)/32 : ℕ) : ℚ≥0))/(p-2 : ℕ) := min_le_right _ _
  have hrQ := NNRat.coe_le_coe.mpr hr
  apply NNRat.coe_le_coe.mp
  norm_num [certifiedEnvelope3125, h, sharpA, sharpComplement, q, p] at hrQ ⊢
  nlinarith
-- CHECKPOINT

theorem phenh_sharp_arithmetic :
    (170906186782 : ℚ≥0)/q^2 < 1/2^90 ∧
    (170906186782 : ℚ≥0)/(q*(q-561 : ℕ)) < 1/2^90 ∧
    (1 : ℚ≥0)/2^90 < 1/2^87 := by
  constructor
  · apply NNRat.coe_lt_coe.mp; norm_num [q]
  constructor <;> apply NNRat.coe_lt_coe.mp <;> norm_num [q]
-- CHECKPOINT

end ProvenHashes.UMASH
