import ProvenHashes.UMASHCarryless
import ProvenHashes.UMASHObligations
import ProvenHashes.UMASHProjection

namespace ProvenHashes.UMASH

/-- Discharges the original PH slice obligation for the literal loop. -/
theorem ph_xor_slice_injective : PHXorSliceInjective := by
  intro u v delta huv a b hab
  have hne : u ^^^ v ≠ 0 := fun h => huv (BitVec.xor_eq_zero_iff.mp h)
  apply clmul_left_injective hne
  have he (k : Word) : clmul u k ^^^ clmul v (k ^^^ delta) =
      clmul (u ^^^ v) k ^^^ clmul v delta := by
    rw [clmul_xor_right, clmul_xor_left, BitVec.xor_assoc]
  dsimp only at hab
  rw [he, he, BitVec.xor_left_inj] at hab
  exact hab
-- CHECKPOINT

theorem split_injective : Function.Injective split := by
  intro a b heq
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  by_cases hlo : n < 64
  · have he := congrArg (fun z : Chunk => z.1.getLsbD n) heq
    simpa [split, hlo] using he
  · have he := congrArg (fun z : Chunk => z.2.getLsbD (n-64)) heq
    simpa [split, show n-64 < 64 by omega, show 64+(n-64) = n by omega] using he
-- CHECKPOINT

theorem split_xor (a b : Wide) : split (a ^^^ b) = xorChunk (split a) (split b) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;>
    intro n hn <;> simp [split, xorChunk, hn]
-- CHECKPOINT

/-- Transfer the 852-mask cover directly to full carry-less products. -/
theorem projected_wide_xor_bound {K : Type*} [Fintype K]
    (x y : K → Wide) (hinj : Function.Injective (fun k => x k ^^^ y k)) :
    uniformProb (fun k => project (split (x k)) = project (split (y k))) ≤
      (852 : ℚ≥0)^2 / (Fintype.card K : ℚ≥0) := by
  apply projected_collision_mask_bound
  intro a b heq
  apply hinj
  apply split_injective
  rw [split_xor, split_xor]
  apply Prod.ext
  · apply BitVec.eq_of_toNat_eq
    simpa only [xorChunk, BitVec.toNat_xor] using congrArg Prod.fst heq
  · apply BitVec.eq_of_toNat_eq
    simpa only [xorChunk, BitVec.toNat_xor] using congrArg Prod.snd heq
-- CHECKPOINT

theorem ph_affine_xor_injective (u v delta : Word) (A B : Wide) (huv : u ≠ v) :
    Function.Injective (fun k : Word =>
      (clmul u k ^^^ A) ^^^ (clmul v (k ^^^ delta) ^^^ B)) := by
  intro a b hab
  have he (k : Word) : (clmul u k ^^^ A) ^^^ (clmul v (k ^^^ delta) ^^^ B) =
      (clmul u k ^^^ clmul v (k ^^^ delta)) ^^^ (A ^^^ B) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  dsimp only at hab
  rw [he, he, BitVec.xor_left_inj] at hab
  exact ph_xor_slice_injective u v delta huv hab
-- CHECKPOINT

/-- The exact paper bound for a conditioned PH slice, with both common or
different fixed contributions and an arbitrary key-translation delta. -/
theorem ph_slice_projected_bound (u v delta : Word) (A B : Wide) (huv : u ≠ v) :
    uniformProb (fun k : Word =>
      project (split (clmul u k ^^^ A)) =
      project (split (clmul v (k ^^^ delta) ^^^ B))) ≤ (852 : ℚ≥0)^2/q := by
  have hw : Fintype.card Word = q :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin q)
  simpa only [hw] using projected_wide_xor_bound
    (fun k => clmul u k ^^^ A) (fun k => clmul v (k ^^^ delta) ^^^ B)
    (ph_affine_xor_injective u v delta A B huv)
-- CHECKPOINT

end ProvenHashes.UMASH
