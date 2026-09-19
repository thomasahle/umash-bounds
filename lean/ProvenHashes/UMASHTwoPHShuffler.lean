import ProvenHashes.UMASHShufflerKernel
import ProvenHashes.UMASHRank

/-! Two-PH shuffler elimination. The argument from the GPT-6 Pro handoff
of 2026-09-19, restricted joint reduction §1.2, uses the kernel of the
difference of two actual nonfinal shufflers. All lane identities below
are width-uniform and retain the reference's exceptional distance-one case. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

theorem twoPH_lane_xor {n : ℕ} (s : ℕ) (x y : BitVec n) :
    phShuffleLane s (x ^^^ y) = phShuffleLane s x ^^^ phShuffleLane s y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [phShuffleLane]
  split_ifs <;>
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft] <;>
    cases x.getLsbD (i-1) <;> cases y.getLsbD (i-1) <;>
    cases x.getLsbD (i-s) <;> cases y.getLsbD (i-s) <;>
    simp [hi, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

def phDifferenceShift (s t : ℕ) : ℕ := if t = 1 then s else t

theorem phShuffleLane_difference_eq_iff {n : ℕ} (s t : ℕ)
    (ht : 0 < t) (hst : t < s) (x y : BitVec n) :
    (phShuffleLane s x ^^^ phShuffleLane t x =
      phShuffleLane s y ^^^ phShuffleLane t y) ↔
    x <<< phDifferenceShift s t = y <<< phDifferenceShift s t := by
  have hs : s ≠ 1 := by omega
  by_cases ht1 : t = 1
  · have hf (z : BitVec n) : phShuffleLane s z ^^^ phShuffleLane t z = z <<< s := by
      simp only [phShuffleLane, ht1, hs, ↓reduceIte]
      rw [BitVec.xor_comm (z <<< 1) (z <<< s), BitVec.xor_assoc,
        BitVec.xor_self, BitVec.xor_zero]
    rw [hf x, hf y]
    simp only [phDifferenceShift, ht1, ↓reduceIte]
  · have hf (z : BitVec n) :
        phShuffleLane s z ^^^ phShuffleLane t z =
        (z <<< t) ^^^ ((z <<< t) <<< (s-t)) := by
      simp only [phShuffleLane, hs, ht1, ↓reduceIte, ← BitVec.shiftLeft_add,
        show t+(s-t) = s by omega]
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm,
        Bool.xor_comm, Bool.xor_self, Bool.xor_false, Bool.false_xor]
    rw [hf x, hf y]
    simpa only [phDifferenceShift, ht1, ↓reduceIte] using
      (xor_left_shift_injective n (s-t) (by omega)).eq_iff
-- CHECKPOINT

def phShuffleChunk (s : ℕ) (x : Chunk) : Chunk :=
  (phShuffleLane s x.1, phShuffleLane s x.2)

def phShuffleDifference (s t : ℕ) (x : Chunk) : Chunk :=
  xorChunk (phShuffleChunk s x) (phShuffleChunk t x)

theorem phShuffleChunk_xor (s : ℕ) (x y : Chunk) :
    phShuffleChunk s (xorChunk x y) = xorChunk (phShuffleChunk s x) (phShuffleChunk s y) := by
  exact Prod.ext (twoPH_lane_xor s x.1 y.1) (twoPH_lane_xor s x.2 y.2)
-- CHECKPOINT

theorem phShuffleDifference_eq_iff (s t : ℕ) (ht : 0 < t) (hst : t < s)
    (x y : Chunk) : phShuffleDifference s t x = phShuffleDifference s t y ↔
    laneShift x (phDifferenceShift s t) = laneShift y (phDifferenceShift s t) := by
  simp only [phShuffleDifference, phShuffleChunk, xorChunk, laneShift, Prod.mk.injEq]
  rw [phShuffleLane_difference_eq_iff s t ht hst x.1 y.1,
    phShuffleLane_difference_eq_iff s t ht hst x.2 y.2]
-- CHECKPOINT

theorem laneShift_xor_cancel (x y c : Chunk) (h : ℕ) :
    laneShift (xorChunk x c) h = laneShift (xorChunk y c) h ↔
    laneShift x h = laneShift y h := by
  have hf (a b : Word) : (a ^^^ b) <<< h = (a <<< h) ^^^ (b <<< h) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft]
    by_cases hh : i < h <;> simp [hi, hh]
  simp only [laneShift, xorChunk, hf, Prod.mk.injEq, BitVec.xor_left_inj]
-- CHECKPOINT

/-- The difference of two literal PH shufflers loses at most h bits of
entropy on every nonzero carryless slice, even after an affine translation. -/
theorem two_ph_shifted_slice_count (d : Word) (hd : d ≠ 0) (c z : Chunk)
    (s t : ℕ) (ht : 0 < t) (hst : t < s) (hs : s ≤ 64) :
    (Finset.univ.filter (fun k : Word =>
      phShuffleDifference s t (xorChunk (split (clmul d k)) c) = z)).card ≤
    2^(phDifferenceShift s t) := by
  classical
  let E (k : Word) := phShuffleDifference s t (xorChunk (split (clmul d k)) c) = z
  by_cases hex : ∃ k, E k
  · obtain ⟨k₀,hk₀⟩ := hex
    have hh : phDifferenceShift s t ≤ 64 := by
      unfold phDifferenceShift
      split_ifs <;> omega
    apply (Finset.card_le_card ?_).trans
      (rank_lemma64 d hd (phDifferenceShift s t) hh
        (laneShift (split (clmul d k₀)) (phDifferenceShift s t)))
    intro k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply (laneShift_xor_cancel _ _ c _).mp
    apply (phShuffleDifference_eq_iff s t ht hst _ _).mp
    exact (Finset.mem_filter.mp hk).2.trans hk₀.symm
  · have hz : (Finset.univ.filter E) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      exact hex ⟨k,(Finset.mem_filter.mp hk).2⟩
    change (Finset.univ.filter E).card ≤ _
    rw [hz, Finset.card_empty]
    exact Nat.zero_le _
-- CHECKPOINT

end ProvenHashes.UMASH
