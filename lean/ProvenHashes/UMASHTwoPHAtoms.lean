import ProvenHashes.UMASHTwoPHShuffler
import ProvenHashes.UMASHPHDifference
import ProvenHashes.UMASHJointProbability

/-! Conditional two-PH atoms, following the argument from the GPT-6 Pro
handoff of 2026-09-19, restricted joint reduction §1.2. The two coordinates
are independent before rejection sampling; no independence of the completed
compressors is asserted. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

theorem ph_right_difference_affine (x y : Chunk) (fixed k : Word) :
    xorChunk (ph (fixed,k) x) (ph (fixed,k) y) =
    xorChunk (split (clmul (x.1 ^^^ y.1) k))
      (split (clmul (x.1 ^^^ fixed) x.2 ^^^ clmul (y.1 ^^^ fixed) y.2)) := by
  rw [ph, ph, ← split_xor, ← split_xor]
  apply congrArg split
  simp only [clmul_xor_right, clmul_xor_left]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp [BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm,
    Bool.xor_comm, Bool.xor_self, Bool.xor_false, Bool.false_xor]
-- CHECKPOINT

theorem two_ph_shifted_slice_probability (d : Word) (hd : d ≠ 0) (c z : Chunk)
    (s t : ℕ) (ht : 0 < t) (hst : t < s) (hs : s ≤ 64) :
    uniformProb (fun k : Word =>
      phShuffleDifference s t (xorChunk (split (clmul d k)) c) = z) ≤
    (2:ℚ≥0)^(phDifferenceShift s t)/q := by
  have hc := two_ph_shifted_slice_count d hd c z s t ht hst hs
  unfold uniformProb
  rw [word_card]
  apply div_le_div_of_nonneg_right _ (zero_le _)
  have hh := (Nat.cast_le (α := ℚ≥0)).mpr hc
  convert hh using 1
  · congr 1
    apply congrArg Finset.card
    ext k
    simp
  · simp
-- CHECKPOINT

theorem ph_shuffler_difference_probability (x y z : Chunk) (hxy : x ≠ y)
    (s t : ℕ) (ht : 0 < t) (hst : t < s) (hs : s ≤ 64) :
    uniformProb (fun k : Chunk =>
      phShuffleDifference s t (xorChunk (ph k x) (ph k y)) = z) ≤
    (2:ℚ≥0)^(phDifferenceShift s t)/q := by
  have hright (a b : Chunk) (hab : a.1 ≠ b.1) :
      uniformProb (fun k : Chunk =>
        phShuffleDifference s t (xorChunk (ph k a) (ph k b)) = z) ≤
      (2:ℚ≥0)^(phDifferenceShift s t)/q := by
    apply probability_prod_le
    intro fixed
    simp_rw [ph_right_difference_affine]
    exact two_ph_shifted_slice_probability _
      (fun h => hab (BitVec.xor_eq_zero_iff.mp h)) _ z s t ht hst hs
  by_cases hx : x.1 ≠ y.1
  · exact hright x y hx
  · have hy : x.2 ≠ y.2 := by
      intro h
      exact hxy (Prod.ext (not_ne_iff.mp hx) h)
    rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => phShuffleDifference s t (xorChunk (ph k x) (ph k y)) = z)]
    simpa only [ph, clmul_comm] using hright (x.2,x.1) (y.2,y.1) hy
-- CHECKPOINT

theorem two_ph_eliminate (s t : ℕ) (a b u v : Chunk)
    (hu : xorChunk a b = u)
    (hv : xorChunk (phShuffleChunk s a) (phShuffleChunk t b) = v) :
    phShuffleDifference s t b = xorChunk (phShuffleChunk s u) v := by
  calc
    _ = xorChunk (xorChunk (phShuffleChunk s a) (phShuffleChunk s b))
        (xorChunk (phShuffleChunk s a) (phShuffleChunk t b)) := by
      apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i _ <;>
        simp [phShuffleDifference, xorChunk, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
    _ = _ := by rw [← phShuffleChunk_xor, hu, hv]
-- CHECKPOINT

/-- The joint full-output atom for two independent changed PH chunks. -/
theorem two_ph_joint_atom (x y x' y' u v : Chunk)
    (hxy : x ≠ y) (hxy' : x' ≠ y') (s t : ℕ)
    (ht : 0 < t) (hst : t < s) (hs : s ≤ 64) :
    uniformProb (fun ab : Chunk × Chunk =>
      xorChunk (xorChunk (ph ab.1 x) (ph ab.1 y))
        (xorChunk (ph ab.2 x') (ph ab.2 y')) = u ∧
      xorChunk (phShuffleChunk s (xorChunk (ph ab.1 x) (ph ab.1 y)))
        (phShuffleChunk t (xorChunk (ph ab.2 x') (ph ab.2 y'))) = v) ≤
    (2:ℚ≥0)^(phDifferenceShift s t)/q^2 := by
  let A (k : Chunk) := xorChunk (ph k x) (ph k y)
  let B (k : Chunk) := xorChunk (ph k x') (ph k y')
  let E (k : Chunk) := phShuffleDifference s t (B k) = xorChunk (phShuffleChunk s u) v
  let F (ba : Chunk × Chunk) := xorChunk (A ba.2) (B ba.1) = u
  rw [← uniformProb_equiv (Equiv.prodComm Chunk Chunk)]
  have hcover : uniformProb (fun ba : Chunk × Chunk =>
      xorChunk (A ba.2) (B ba.1) = u ∧
      xorChunk (phShuffleChunk s (A ba.2)) (phShuffleChunk t (B ba.1)) = v) ≤
      uniformProb (fun ba : Chunk × Chunk => E ba.1 ∧ F ba) := by
    apply probability_mono
    intro ba h
    exact ⟨two_ph_eliminate s t (A ba.2) (B ba.1) u v h.1 h.2, h.1⟩
  apply hcover.trans
  have hF : ∀ b, uniformProb (fun a => F (b,a)) ≤ (1:ℚ≥0)/q := by
    intro b
    apply (probability_mono ?_).trans (ph_xor_target_probability x y (xorChunk u (B b)) hxy)
    intro a ha
    have he := congrArg (fun z => xorChunk z (B b)) ha
    simpa only [F, xorChunk, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using he
  calc
    _ ≤ uniformProb E*((1:ℚ≥0)/q) := probability_and_prod_le E F _ hF
    _ ≤ ((2:ℚ≥0)^(phDifferenceShift s t)/q)*((1:ℚ≥0)/q) :=
      mul_le_mul_of_nonneg_right
        (ph_shuffler_difference_probability x' y' _ hxy' s t ht hst hs) (zero_le _)
    _ = _ := by ring
-- CHECKPOINT

end ProvenHashes.UMASH
