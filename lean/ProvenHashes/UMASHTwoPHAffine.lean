import ProvenHashes.UMASHTwoPHCompatibility

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb ph clmul

theorem xorChunk_cancel_right (a b : Chunk) : xorChunk (xorChunk a b) b = a := by
  apply Prod.ext <;> simp only [xorChunk, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
-- CHECKPOINT

theorem two_ph_affine_atom (x y x' y' C D u v : Chunk)
    (hxy : x ≠ y) (hxy' : x' ≠ y') (s t : ℕ)
    (ht : 0 < t) (hst : t < s) (hs : s ≤ 64) :
    uniformProb (fun ab : Chunk × Chunk =>
      xorChunk (xorChunk (xorChunk (ph ab.1 x) (ph ab.1 y))
        (xorChunk (ph ab.2 x') (ph ab.2 y'))) C = u ∧
      xorChunk (xorChunk (phShuffleChunk s (xorChunk (ph ab.1 x) (ph ab.1 y)))
        (phShuffleChunk t (xorChunk (ph ab.2 x') (ph ab.2 y')))) D = v) ≤
    (2:ℚ≥0)^(phDifferenceShift s t)/q^2 := by
  apply (probability_mono ?_).trans
    (two_ph_joint_atom x y x' y' (xorChunk u C) (xorChunk v D) hxy hxy' s t ht hst hs)
  intro ab h
  exact ⟨by simpa only [xorChunk_cancel_right] using congrArg (fun z => xorChunk z C) h.1,
    by simpa only [xorChunk_cancel_right] using congrArg (fun z => xorChunk z D) h.2⟩
-- CHECKPOINT

theorem two_ph_affine_compatibility (s t : ℕ) (ht : 0 < t) (hst : t < s)
    (hh : 3 ≤ phDifferenceShift s t) (a b C D : Chunk) :
    let U := xorChunk (xorChunk a b) C
    let V := xorChunk (xorChunk (phShuffleChunk s a) (phShuffleChunk t b)) D
    (V.1.toNat ^^^ (2*U.1.toNat))%8 = (D.1 ^^^ (C.1 <<< 1)).toNat%8 ∧
    (V.2.toNat ^^^ (2*U.2.toNat))%8 = (D.2 ^^^ (C.2 <<< 1)).toNat%8 := by
  exact ⟨two_ph_three_bit_compatibility s t ht hst hh a.1 b.1 C.1 D.1,
    two_ph_three_bit_compatibility s t ht hst hh a.2 b.2 C.2 D.2⟩
-- CHECKPOINT

end ProvenHashes.UMASH
