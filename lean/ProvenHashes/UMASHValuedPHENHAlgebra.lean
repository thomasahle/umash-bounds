import ProvenHashes.UMASHChunkValuation
import ProvenHashes.UMASHPHENHAlgebra

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] ph clmul maskSet uniformProb

theorem valued_ph_low_divisible (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hv : ChunkValuation (lastChunk x) (lastChunk y) r) :
    2^r ∣ (blockPHDelta k x y i).1.toNat ∧
      2^r ∣ (blockENHDelta k seed x y).1.toNat := by
  have h1 := hv.fst_dvd
  have h2 := hv.snd_dvd
  have hd := single_ph_checksum_difference x y hc hs i hi ho
  have hP1 : 2^r ∣ ((x.chunks.getD i (0,0)).1 ^^^ (y.chunks.getD i (0,0)).1).toNat := by
    change 2^r ∣ (xorChunk (x.chunks.getD i (0,0)) (y.chunks.getD i (0,0))).1.toNat
    rw [hd]
    exact h1
  have hP2 : 2^r ∣ ((x.chunks.getD i (0,0)).2 ^^^ (y.chunks.getD i (0,0)).2).toNat := by
    change 2^r ∣ (xorChunk (x.chunks.getD i (0,0)) (y.chunks.getD i (0,0))).2.toNat
    rw [hd]
    exact h2
  exact ⟨(word_prefix_eq_iff_xor_dvd _ _ r).mp
      (ph_low_prefix _ _ _ r hv.lt64.le hP1 hP2),
    (word_prefix_eq_iff_xor_dvd _ _ r).mp
      (enh_low_prefix _ _ _ _ _ r hv.lt64.le h1 h2)⟩
-- CHECKPOINT

/-- Both observed low masks lie in D intersect 2^r Z. -/
theorem valued_ph_joint_low_masks (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hv : ChunkValuation (lastChunk x) (lastChunk y) r)
    (he : jointEvent seed x y k) :
    (rawPrimaryMask k seed x y).1.toNat ∈ valuationMasks r ∧
      (rawSecondaryMask k seed x y).1.toNat ∈ valuationMasks r := by
  obtain ⟨hp,he'⟩ := valued_ph_low_divisible k seed x y hc hs i hi ho r hv
  have hm := joint_event_raw_masks k seed x y hc hs he
  have ha := single_ph_raw_algebra k seed x y hc i hi ho
  have hp0 := Nat.mod_eq_zero_of_dvd hp
  have he0 := Nat.mod_eq_zero_of_dvd he'
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_product.mp hm.1).1, ?_⟩
    rw [ha.1]
    change ((blockPHDelta k x y i).1 ^^^ (blockENHDelta k seed x y).1).toNat%2^r = 0
    rw [BitVec.toNat_xor, Nat.xor_mod_two_pow, hp0, he0, Nat.xor_self]
  · apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_product.mp hm.2).1, ?_⟩
    rw [ha.2]
    change ((phShuffleLane (x.chunks.length-(i+1)) (blockPHDelta k x y i).1) ^^^
      (blockENHDelta k seed x y).1).toNat%2^r = 0
    rw [BitVec.toNat_xor, Nat.xor_mod_two_pow,
      phShuffleLane_prefix_zero _ r hv.lt64.le _ hp0, he0, Nat.xor_self]
-- CHECKPOINT

/-- PROOF2 reduction (8) on the actual block compressor: at r ≥ 4,
a joint projected collision forces both separate low differences to zero. -/
theorem valued_ph_joint_low_zero (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hv : ChunkValuation (lastChunk x) (lastChunk y) r) (hr4 : 4 ≤ r)
    (he : jointEvent seed x y k) :
    (blockPHDelta k x y i).1 = 0 ∧ (blockENHDelta k seed x y).1 = 0 := by
  obtain ⟨hp,he'⟩ := valued_ph_low_divisible k seed x y hc hs i hi ho r hv
  have hm := joint_event_raw_masks k seed x y hc hs he
  have ha := single_ph_raw_algebra k seed x y hc i hi ho
  have hpm := (Finset.mem_product.mp hm.1).1
  have hsm := (Finset.mem_product.mp hm.2).1
  rw [ha.1] at hpm
  rw [ha.2] at hsm
  exact phenh_low_reduction (x.chunks.length-(i+1)) (by omega)
    (blockPHDelta k x y i).1 (blockENHDelta k seed x y).1
    ((pow_dvd_pow 2 hr4).trans hp) ((pow_dvd_pow 2 hr4).trans he') hpm hsm
-- CHECKPOINT

end ProvenHashes.UMASH
