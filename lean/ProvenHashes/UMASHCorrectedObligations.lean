import ProvenHashes.UMASHConditioning
import ProvenHashes.UMASHENHHighValuation
import ProvenHashes.UMASHENHWords
import ProvenHashes.UMASHProjectionRefined
import ProvenHashes.UMASHPHDifference

/-! Precise proof-obligation signatures for the corrected lane. Some are discharged
in subsequent modules; STATUS.md records what remains. These definitions do not
postulate any probabilistic statement. -/
namespace ProvenHashes.UMASH

def LowAdditiveDistribution : Prop := ∀ r δ ε : ℕ,
  r < 64 → 2^r ∣ δ → 2^r ∣ ε → (δ/2^r)%2 = 1 →
  ∀ t : Fin (q/2^r),
  uniformProb (fun ab : Word × Word =>
    (δ : ZMod q)*(ab.2.toNat : ZMod q) + (ε : ZMod q)*(ab.1.toNat : ZMod q) +
      (δ : ZMod q)*(ε : ZMod q) = ((2^r*t.val : ℕ) : ZMod q)) = ((2^r : ℕ) : ℚ≥0)/q

def LowProjectionBound : Prop := ∀ r δ ε M : ℕ,
  r < 64 → 2^r ∣ δ → 2^r ∣ ε → (δ/2^r)%2 = 1 → M < q →
  uniformProb (fun ab : Word × Word =>
    (M ^^^ (ab.1.toNat*ab.2.toNat%q))%p =
    (M ^^^ (((ab.1.toNat+δ)%q)*((ab.2.toNat+ε)%q)%q))%p) ≤
      ((2^r*patternWeight r : ℕ) : ℚ≥0)/q

def PrimaryENHOnlyBound : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → phDiffCount x y = 0 → lastChunk x ≠ lastChunk y →
  uniformProb (primaryEvent seed x y) ≤ (5542:ℚ≥0)/q

def JointENHOnlyBound : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → phDiffCount x y = 0 → lastChunk x ≠ lastChunk y →
  uniformProb (jointEvent seed x y) ≤ (4721784:ℚ≥0)/q^2

def LowPHDistribution : Prop := ∀ (d : Word), d ≠ 0 →
  ∀ r : ℕ, r = padicValNat 2 d.toNat → ∀ z : Word, 2^r ∣ z.toNat →
  uniformProb (fun k : Word => (split (clmul d k)).1 = z) = ((2^r : ℕ) : ℚ≥0)/q

def EvenPHBound : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → 0 < phDiffCount x y → ¬oddPH x y →
  uniformProb (primaryEvent seed x y) ≤ (364816:ℚ≥0)/q

def HighProductPointMass : Prop := ∀ h : ℕ,
  uniformProb (fun ab : Word × Word => ab.1.toNat*ab.2.toNat/q = h) < (66:ℚ≥0)/q

def ENHProjectedPointMass : Prop := ∀ (tag : Word) (M : Chunk) (z : Field × Field),
  uniformProb (fun k : Chunk => project (xorChunk M (enh k (0,0) tag)) = z) ≤
    ((82*q-81 : ℕ) : ℚ≥0)/(q:ℚ≥0)^2

def CorrectedDifferentChunkCountsBound : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → ¬sameCount x y →
  uniformProb (primaryEvent seed x y) < (82:ℚ≥0)/q

def PrimaryTagOnlyBound : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → x.chunks = y.chunks → blockTag seed x ≠ blockTag seed y →
  uniformProb (primaryEvent seed x y) < (269280:ℚ≥0)/q

def CorrectedPrimaryBlockBound : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → (x.chunks ≠ y.chunks ∨ blockTag seed x ≠ blockTag seed y) →
  uniformProb (primaryEvent seed x y) ≤ (364816:ℚ≥0)/q

def ShortMessageUniform : Prop := ∀ (seed : Word) (m : Message),
  m.length ≤ 8 → ∀ t : Word,
  uniformProb (fun k : OHKey => shortHash k seed m false = t) = (1:ℚ≥0)/q

def ShortEqualLengthInjective : Prop := ∀ (seed : Word) (k : OHKey) (x y : Message),
  x.length ≤ 8 → x.length = y.length →
  shortHash k seed x false = shortHash k seed y false → x = y

def ShortDifferentLengthCollision : Prop := ∀ (seed : Word) (x y : Message),
  x.length ≤ 8 → y.length ≤ 8 → x.length ≠ y.length →
  uniformProb (fun k : OHKey => shortHash k seed x false = shortHash k seed y false) =
    (1:ℚ≥0)/q

def CorrectedDifferentBlockCountsBound : Prop := ∀ (seed : Word) (x y : Message),
  8 < x.length → 8 < y.length → (encode x).length ≠ (encode y).length →
  uniformProb (fun k : OHKey => comparisonPolynomial k seed x = comparisonPolynomial k seed y) <
    (82:ℚ≥0)/q

def CertifiedAllPairs64IID : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : OHKey × PolyKey =>
    hashWith k.1 k.2.val.val seed x = hashWith k.1 k.2.val.val seed y) ≤ certifiedEnvelope L

theorem openENHOnly_of_joint (h : JointENHOnlyBound) : OpenENHOnly := by
  intro seed x y hx hy hc hp he _hr _hr'
  have hne : lastChunk x ≠ lastChunk y := by
    intro hh
    simp [enhChanges, hh] at he
  exact (h seed x y hx hy hc hp hne).trans_lt
    (corrected_joint_arithmetic.1.trans corrected_joint_arithmetic.2.2)
-- CHECKPOINT

end ProvenHashes.UMASH
