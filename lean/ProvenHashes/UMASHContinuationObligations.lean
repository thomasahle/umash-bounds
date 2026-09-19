import ProvenHashes.UMASHSharpObligations
import ProvenHashes.UMASHQuadraticSets

/-! Precise remaining targets for the next continuation. These are definitions
of propositions, not assumptions or proofs of any collision bound. -/
namespace ProvenHashes.UMASH

/-- PROOF2 Lemma 4.1, stated for every finite set of integer preimages. -/
def QuadraticIntervalCount : Prop :=
  ∀ (m : ℕ) (lo hi : Fin m → ℝ) (ell : ℝ) (a b c : ℤ) (T : Finset ℤ),
    0 < m → 0 < ell → a ≠ 0 →
    (∀ i, lo i ≤ hi i ∧ hi i-lo i ≤ ell) →
    (∀ i j, i ≠ j → Disjoint (Set.Ico (lo i) (hi i)) (Set.Ico (lo j) (hi j))) →
    (∀ t ∈ T, ∃ i, lo i ≤ (quadraticValue a b c t : ℝ) ∧
      (quadraticValue a b c t : ℝ) < hi i) →
    (T.card : ℝ) ≤ 2*Real.sqrt ((m:ℝ)*ell/|(a:ℝ)|)+2*m

def SecondaryBlockBound729632 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → (x.chunks ≠ y.chunks ∨ blockTag seed x ≠ blockTag seed y) →
  uniformProb (fun k : OHKey => project (ohSecondary k x seed) =
    project (ohSecondary k y seed)) ≤ (729632:ℚ≥0)/q

def JointBlockBound1416246956032 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → (x.chunks ≠ y.chunks ∨ blockTag seed x ≠ blockTag seed y) →
  uniformProb (jointEvent seed x y) ≤ (1416246956032:ℚ≥0)/q^2

def headlineA : ℚ≥0 := (205:ℚ≥0)/(q-561:ℕ)
def headlineS : ℚ≥0 := (435:ℚ≥0)/(q-561:ℕ)+2/(p-2:ℕ)
def headlineEnvelope (L : ℕ) : ℚ≥0 :=
  if L = 1 then (1:ℚ≥0)/(q-561:ℕ)
  else max (headlineA+(1-headlineA)*rootRate L) headlineS

def Published64Envelope : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤ headlineEnvelope L

def Published64Strong : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) <
    58*(((L+511)/512:ℕ):ℚ≥0)/2^61

def Published64StrongIID : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : OHKey × PolyKey =>
    hashWith k.1 k.2.val.val seed x = hashWith k.1 k.2.val.val seed y) <
    58*(((L+511)/512:ℕ):ℚ≥0)/2^61

def Published128Inherited58 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) <
    58*(((L+511)/512:ℕ):ℚ≥0)/2^61

def publishedFingerprintNumerator (L : ℕ) : ℚ≥0 :=
  (81:ℚ≥0)/128*((((L+2^23-1)/2^23:ℕ):ℚ≥0)^2)/2^83

def Published128Strong : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) <
    publishedFingerprintNumerator L

def Published128StrongIID : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : OHKey × (PolyKey × PolyKey) =>
    (hashWith k.1 k.2.1.val.val seed x, hashWith k.1 k.2.2.val.val seed x true) =
    (hashWith k.1 k.2.1.val.val seed y, hashWith k.1 k.2.2.val.val seed y true)) <
    publishedFingerprintNumerator L

abbrev NonzeroPolyKey := {f : Fin p // 0 < f.val}
noncomputable instance nonzeroPolyKeyFintype : Fintype NonzeroPolyKey := Fintype.ofFinite _

def Published128StrongNonzero : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : DistinctOHKey × (NonzeroPolyKey × NonzeroPolyKey) =>
    (hashWith k.1.val k.2.1.val.val seed x, hashWith k.1.val k.2.2.val.val seed x true) =
    (hashWith k.1.val k.2.1.val.val seed y, hashWith k.1.val k.2.2.val.val seed y true)) <
    publishedFingerprintNumerator L

def Published128StrongIIDNonzero : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : OHKey × (NonzeroPolyKey × NonzeroPolyKey) =>
    (hashWith k.1 k.2.1.val.val seed x, hashWith k.1 k.2.2.val.val seed x true) =
    (hashWith k.1 k.2.1.val.val seed y, hashWith k.1 k.2.2.val.val seed y true)) <
    publishedFingerprintNumerator L

def referenceSwapX : Message := List.replicate 256 0 ++ List.replicate 256 1
def referenceSwapY : Message := List.replicate 256 1 ++ List.replicate 256 0

def ReferenceSwapCollision : Prop := ∀ (k : OHKey) (seed : Word),
  (hashWith k (p-1) seed referenceSwapX, hashWith k (p-1) seed referenceSwapX true) =
  (hashWith k (p-1) seed referenceSwapY, hashWith k (p-1) seed referenceSwapY true)

def ReferenceSwapLowerBound : Prop := ∀ (seed : Word),
  (1:ℚ≥0)/(p-2:ℕ) ≤ uniformProb (fun k : Key64 =>
    referenceFingerprint k seed referenceSwapX = referenceFingerprint k seed referenceSwapY)

end ProvenHashes.UMASH
