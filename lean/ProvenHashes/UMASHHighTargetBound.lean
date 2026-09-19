import ProvenHashes.UMASHHighXorDense

namespace ProvenHashes.UMASH

/-- The three terms of PROOF2 (14), with the certificate's ceiling exponent. -/
def highTargetK (e : ℕ) : ℚ≥0 :=
  min ((2:ℚ≥0)^(1+(maskBitSet 64 e).card-(if e.testBit 63 then 1 else 0)))
    (min ((276:ℚ≥0)*2^(64-(maskBitSet 64 e).card))
      (16*((2:ℚ≥0)^(((maskBitSet 64 e).card+1)/2)+1)))

/-- PROOF2 Lemma 4.3, including every term of K_H and arbitrary tags.
No minimum-valuation premise is needed. -/
theorem high_enh_target_bound (δ ε tag tag' e : ℕ)
    (hδ : 0 < δ ∧ δ < q) (hε : 0 < ε ∧ ε < q) :
    uniformProb (fun ab : Word × Word =>
      highXorEventNat 64 δ ε tag tag' e (ab.1.toNat, ab.2.toNat)) ≤ highTargetK e/q := by
  have hq : (0:ℚ≥0) < q := by norm_num [q]
  have hs := high_xor_sparse_probability_word δ ε tag tag' e hδ hε.2
  have hd := (probability_mono (fun (ab : Word × Word)
    (he : highXorEventNat 64 δ ε tag tag' e (ab.1.toNat,ab.2.toNat)) =>
      show highTaggedXorEventNat 64 δ ε tag tag' e (ab.1.toNat,ab.2.toNat) from he.2)).trans
    (high_xor_dense_probability_word δ ε tag tag' e hδ hε.2)
  have hc := high_xor_quadratic_probability_word δ ε tag tag' e hδ hε
  apply (le_div_iff₀ hq).mpr
  refine le_min ?_ (le_min ((le_div_iff₀ hq).mp hd) ((le_div_iff₀ hq).mp hc))
  apply ((le_div_iff₀ hq).mp hs).trans
  apply pow_le_pow_right₀ (by norm_num : (1:ℚ≥0) ≤ 2)
  split_ifs <;> omega
-- CHECKPOINT

end ProvenHashes.UMASH
