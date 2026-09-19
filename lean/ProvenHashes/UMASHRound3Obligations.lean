import ProvenHashes.UMASHHighXorSparse
import ProvenHashes.UMASHLowXorUniform

/-! Checked definitions of the next analytic obligations in PROOF2.
These declarations do not postulate or prove either probability bound. -/
namespace ProvenHashes.UMASH

def highTaggedXorEventNat (n δ ε tag tag' e : ℕ) (ab : ℕ × ℕ) : Prop :=
  ((ab.1*ab.2/2^n+tag)%2^n) ^^^
    (((((ab.1+δ)%2^n)*((ab.2+ε)%2^n))/2^n+tag')%2^n) = e

/-- PROOF2 Lemma 4.3's dense-mask term, without a low-word equality premise. -/
def HighENHDenseBound : Prop := ∀ (δ ε tag tag' e : ℕ),
  0 < δ → δ < q → 0 < ε → ε < q → e < q →
  uniformProb (fun ab : Word × Word =>
    highTaggedXorEventNat 64 δ ε tag tag' e (ab.1.toNat, ab.2.toNat)) ≤
    (276:ℚ≥0)*2^(64-(maskBitSet 64 e).card)/q

def lowTargetK (r e : ℕ) : ℚ≥0 :=
  if e = 0 then 2^r else
    min ((2:ℚ≥0)^r*2^((maskBitSet 64 e).card-(if e.testBit 63 then 1 else 0)))
      (min ((65:ℚ≥0)*2^(64-(maskBitSet 64 e).card))
        (4*(2:ℚ≥0)^r*2^(((maskBitSet 64 e).card+1)/2)))

/-- PROOF2 Lemma 5.2, with only r >= 1 and the stated minimum valuation. -/
def LowENHTargetBound : Prop := ∀ (δ ε r e : ℕ),
  0 < δ → δ < q → 0 < ε → ε < q →
  r = min (padicValNat 2 δ) (padicValNat 2 ε) → 1 ≤ r → e < q → 2^r ∣ e →
  uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
    lowTargetK r e/q

end ProvenHashes.UMASH
