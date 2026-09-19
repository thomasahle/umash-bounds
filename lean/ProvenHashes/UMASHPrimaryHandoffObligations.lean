import ProvenHashes.UMASHContinuationObligations

/-! Remaining primary endpoint interfaces for the full-block/last-update
argument from the GPT-6 Pro handoff of 2026-09-19, Sections 6–7.
These are definitions of propositions, never assumptions or axioms. -/
namespace ProvenHashes.UMASH

/-- A sharp marginal is needed only for full earlier blocks on this route. -/
def PrimaryFullBlockBound256 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → x.byteSize = 256 → y.byteSize = 256 → x.chunks ≠ y.chunks →
  uniformProb (primaryEvent seed x y) ≤ (256:ℚ≥0)/q

/-- A direct last-update estimate on the literal modulus 8p. Common prior
accumulators cancel from the equality; zero is the canonical representative. -/
def PrimaryLastUpdateBound503 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → (x.chunks ≠ y.chunks ∨ blockTag seed x ≠ blockTag seed y) →
  uniformProb (fun k : OHKey × PolyKey =>
    polyStep k.2.val.val 0 (oh k.1 x seed) =
      polyStep k.2.val.val 0 (oh k.1 y seed)) < (503:ℚ≥0)/q

/-- The complete message classifier and root/conditioning arithmetic must
connect the two analytic interfaces above to the original target. -/
def PrimaryHandoffAssembly : Prop :=
  PrimaryFullBlockBound256 → PrimaryLastUpdateBound503 → Published64

end ProvenHashes.UMASH
