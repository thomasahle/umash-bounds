import ProvenHashes.UMASHENHTargetWords
import ProvenHashes.UMASHJointOrientation

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet

/-- The low PH XOR point bound at the actual minimum input valuation.
Both coordinate differences are nonzero in the PH+ENH case. -/
theorem ph_low_xor_target_probability (x y : Chunk) (z : Word)
    (hx : x.1 ≠ y.1) (hy : x.2 ≠ y.2) (r : ℕ)
    (hr : r = min (wordValuation x.1 y.1) (wordValuation x.2 y.2)) :
    uniformProb (fun k : Chunk => (ph k x).1 ^^^ (ph k y).1 = z) ≤
      ((2^r : ℕ) : ℚ≥0)/q := by
  have hs (a b : Chunk) (hab : a.1 ≠ b.1)
      (hval : r = wordValuation a.1 b.1) :
      uniformProb (fun k : Chunk => (ph k a).1 ^^^ (ph k b).1 = z) ≤
        ((2^r : ℕ) : ℚ≥0)/q := by
    apply probability_prod_le
    intro fixed
    have hcancel : (a.1 ^^^ fixed) ^^^ (b.1 ^^^ fixed) = a.1 ^^^ b.1 := by
      rw [BitVec.xor_comm b.1 fixed, BitVec.xor_assoc,
        ← BitVec.xor_assoc fixed fixed b.1, BitVec.xor_self, BitVec.zero_xor]
    have hd : (a.1 ^^^ fixed) ^^^ (b.1 ^^^ fixed) ≠ 0 := by
      rw [hcancel]
      exact fun h => hab (BitVec.xor_eq_zero_iff.mp h)
    have hf (d : Chunk) (k : Word) :
        (ph (fixed,k) d).1 = lowAffinePH (d.1 ^^^ fixed) d.2 0 k := by
      simp only [ph, lowAffinePH]
      rw [BitVec.xor_comm k d.2]
      exact BitVec.zero_xor.symm
    simp only [hf]
    exact low_affine_xor_target_probability _ _ _ _ _ _ z hd r
      (by simpa only [hcancel, wordValuation] using hval)
  rcases le_total (wordValuation x.1 y.1) (wordValuation x.2 y.2) with hle | hle
  · exact hs x y hx (hr.trans (min_eq_left hle))
  · rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => (ph k x).1 ^^^ (ph k y).1 = z)]
    simpa only [ph, clmul_comm] using hs (x.2,x.1) (y.2,y.1) hy (hr.trans (min_eq_right hle))
-- CHECKPOINT

/-- Full 64-by-64 carryless products have degree at most 126. Consequently
the high PH difference has no bit 63, for every key. -/
theorem ph_high_xor_lt (k x y : Chunk) :
    ((ph k x).2 ^^^ (ph k y).2).toNat < 2^63 := by
  have ht : ((ph k x).2 ^^^ (ph k y).2).getLsbD 63 = false := by
    simp only [ph, split, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, show 63 < 64 from by decide, decide_true,
      Bool.true_and, show 63+64 = 127 from rfl, clmul_top_bit, Bool.xor_false]
  have hh := word_top_bit_value ((ph k x).2 ^^^ (ph k y).2)
  rw [ht] at hh
  norm_num at hh ⊢
  omega
-- CHECKPOINT

/-- Independent coordinate events retain the product of their bounds.
This does not assume independence of completed hash compressors. -/
theorem probability_distinct_coordinates_le {I V : Type*} [Fintype I] [Fintype V]
    [Nonempty V] [DecidableEq I] (i j : I) (hij : i ≠ j)
    (P Q : V → Prop) (a b : ℚ≥0) (hP : uniformProb P ≤ a) (hQ : uniformProb Q ≤ b) :
    uniformProb (fun k : I → V => P (k i) ∧ Q (k j)) ≤ a*b := by
  have hbase : uniformProb (fun k : I → V => P (k i)) ≤ a := by
    apply probability_le_of_update _ i
    intro k
    simpa only [Function.update_self] using hP
  have hprod := probability_and_update_le
    (fun k : I → V => P (k i)) (fun k : I → V => Q (k j)) j b
    (by intro k v; simp only [Function.update_of_ne hij])
    (by intro k; simpa only [Function.update_self] using hQ)
  exact hprod.trans (mul_le_mul_of_nonneg_right hbase (by positivity))
-- CHECKPOINT

/-- Partition an event by finitely many raw masks, then average over an
independent twisting coordinate with a mask-dependent conditional weight. -/
theorem probability_partition_update_le {I V T : Type*} [Fintype I] [Fintype V]
    [Nonempty V] [DecidableEq I] (E : (I → V) → Prop) (F : T → (I → V) → Prop)
    (targets : Finset T) (i : I) (count weight : T → ℚ≥0)
    (hcover : ∀ k, E k → ∃ t ∈ targets, F t k)
    (hfixed : ∀ t ∈ targets, ∀ k v, F t (Function.update k i v) ↔ F t k)
    (hslice : ∀ t ∈ targets, ∀ k, F t k →
      uniformProb (fun v => E (Function.update k i v)) ≤ weight t)
    (hcount : ∀ t ∈ targets, uniformProb (F t) ≤ count t) :
    uniformProb E ≤ ∑ t ∈ targets, count t*weight t := by
  calc
    _ ≤ uniformProb (fun k => ∃ t ∈ targets, F t k ∧ E k) := by
      apply probability_mono
      intro k hk
      obtain ⟨t,ht,hF⟩ := hcover k hk
      exact ⟨t,ht,hF,hk⟩
    _ ≤ ∑ t ∈ targets, uniformProb (fun k => F t k ∧ E k) := probability_union_bound _ _
    _ ≤ ∑ t ∈ targets, count t*weight t := by
      apply Finset.sum_le_sum
      intro t ht
      exact (probability_and_update_event_le (F t) E i (weight t)
        (hfixed t ht) (hslice t ht)).trans
        (mul_le_mul_of_nonneg_right (hcount t ht) (by positivity))
-- CHECKPOINT

end ProvenHashes.UMASH
