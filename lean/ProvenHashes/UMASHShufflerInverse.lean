import ProvenHashes.UMASHShufflerElimination

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

/-- Strictly positive lane shifts move agreement on m low bits to agreement
on m+1 low bits. This is the triangular property used by the inverse. -/
theorem phShuffleLane_prefix_step {n : ℕ} (s m : ℕ) (hs : 0 < s)
    (x y : BitVec n) (hxy : ∀ i < m, x.getLsbD i = y.getLsbD i) :
    ∀ i < m+1, (phShuffleLane s x).getLsbD i = (phShuffleLane s y).getLsbD i := by
  intro i hi
  have hshift (k : ℕ) (hk : 0 < k) : (x <<< k).getLsbD i = (y <<< k).getLsbD i := by
    rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
    by_cases hik : i < k
    · simp only [hik, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
    · rw [hxy (i-k) (by omega)]
  unfold phShuffleLane
  split
  · exact hshift 1 (by decide)
  · simp only [BitVec.getLsbD_xor, hshift 1 (by decide), hshift s hs]
-- CHECKPOINT

/-- Fixed-point iteration solves one further low bit at every step. -/
def phShuffleInverseAux {n : ℕ} (s : ℕ) (y : BitVec n) : ℕ → BitVec n
  | 0 => 0
  | m+1 => y ^^^ phShuffleLane s (phShuffleInverseAux s y m)

def phShuffleInverse {n : ℕ} (s : ℕ) (y : BitVec n) : BitVec n :=
  phShuffleInverseAux s y n

theorem phShuffleInverseAux_stable {n : ℕ} (s : ℕ) (hs : 0 < s) (y : BitVec n) (m : ℕ) :
    ∀ i < m, (phShuffleInverseAux s y (m+1)).getLsbD i =
      (phShuffleInverseAux s y m).getLsbD i := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    simp only [phShuffleInverseAux, BitVec.getLsbD_xor]
    congr 1
    exact phShuffleLane_prefix_step s m hs _ _ ih i hi
-- CHECKPOINT

/-- A computable inverse of I+S at every width, including the s=1 case. -/
theorem phShuffleInverse_correct {n : ℕ} (s : ℕ) (hs : 0 < s) (y : BitVec n) :
    phShuffleInverse s y ^^^ phShuffleLane s (phShuffleInverse s y) = y := by
  have hfix : phShuffleInverseAux s y (n+1) = phShuffleInverseAux s y n :=
    BitVec.eq_of_getLsbD_eq (phShuffleInverseAux_stable s hs y n)
  change y ^^^ phShuffleLane s (phShuffleInverse s y) = phShuffleInverse s y at hfix
  have hh := congrArg (fun x : BitVec n => x ^^^ phShuffleLane s (phShuffleInverse s y)) hfix
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using hh.symm
-- CHECKPOINT

theorem phShuffleInverse_left {n : ℕ} (s : ℕ) (hs : 0 < s) (x : BitVec n) :
    phShuffleInverse s (x ^^^ phShuffleLane s x) = x := by
  apply phShuffleLane_add_self_injective n s hs
  exact phShuffleInverse_correct s hs _
-- CHECKPOINT

/-- PROOF2 (7), now with an executable inverse suitable for finite rational
certificates. No surjectivity witness or noncomputable choice is needed. -/
theorem shuffler_elimination_explicit {n : ℕ} (s : ℕ) (hs : 0 < s)
    (x e u v : BitVec n) (hu : x ^^^ e = u) (hv : phShuffleLane s x ^^^ e = v) :
    x = phShuffleInverse s (u ^^^ v) ∧ e = u ^^^ phShuffleInverse s (u ^^^ v) := by
  have heq : x ^^^ phShuffleLane s x = u ^^^ v := by
    rw [← hu, ← hv]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor]
    cases x.getLsbD i <;> cases e.getLsbD i <;>
      cases (phShuffleLane s x).getLsbD i <;> rfl
  have hx : x = phShuffleInverse s (u ^^^ v) := by
    rw [← heq, phShuffleInverse_left s hs]
  refine ⟨hx, ?_⟩
  rw [← hx, ← hu, BitVec.xor_assoc, BitVec.xor_comm e x, ← BitVec.xor_assoc,
    BitVec.xor_self, BitVec.zero_xor]
-- CHECKPOINT

end ProvenHashes.UMASH
