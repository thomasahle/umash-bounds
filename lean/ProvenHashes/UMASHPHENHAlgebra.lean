import ProvenHashes.UMASHShufflerSupport

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] ph clmul maskSet uniformProb

def blockPHDelta (k : OHKey) (x y : Block) (i : ℕ) : Chunk :=
  xorChunk (ph (keyPair k i) (x.chunks.getD i (0,0)))
    (ph (keyPair k i) (y.chunks.getD i (0,0)))

def blockENHDelta (k : OHKey) (seed : Word) (x y : Block) : Chunk :=
  xorChunk (enh (keyPair k (x.chunks.length-1)) (lastChunk x) (blockTag seed x))
    (enh (keyPair k (x.chunks.length-1)) (lastChunk y) (blockTag seed y))

def rawPrimaryMask (k : OHKey) (seed : Word) (x y : Block) : Chunk :=
  xorChunk (oh k x seed) (oh k y seed)

def rawSecondaryMask (k : OHKey) (seed : Word) (x y : Block) : Chunk :=
  xorChunk (secondaryBody k x seed) (secondaryBody k y seed)

/-- Both literal raw mask identities in the notation used by the ledger. -/
theorem single_ph_raw_algebra (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) :
    rawPrimaryMask k seed x y = xorChunk (blockPHDelta k x y i) (blockENHDelta k seed x y) ∧
    rawSecondaryMask k seed x y = xorChunk
      (phShuffleLane (x.chunks.length-(i+1)) (blockPHDelta k x y i).1,
       phShuffleLane (x.chunks.length-(i+1)) (blockPHDelta k x y i).2)
      (blockENHDelta k seed x y) :=
  ⟨single_ph_primary_difference k seed x y hc i hi ho,
   single_ph_secondary_difference k seed x y hc i hi ho⟩
-- CHECKPOINT

/-- Both raw compressor masks belong to the certified projection mask set.
For the secondary body this uses equal checksums to cancel the common twist. -/
theorem joint_event_raw_masks (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y)
    (he : jointEvent seed x y k) :
    ((rawPrimaryMask k seed x y).1.toNat, (rawPrimaryMask k seed x y).2.toNat) ∈
      maskSet ×ˢ maskSet ∧
    ((rawSecondaryMask k seed x y).1.toNat, (rawSecondaryMask k seed x y).2.toNat) ∈
      maskSet ×ˢ maskSet := by
  constructor
  · simpa only [rawPrimaryMask, xorChunk, BitVec.toNat_xor] using
      project_eq_mask_cover (oh k x seed) (oh k y seed) he.1
  · have hm : ((xorChunk (ohSecondary k x seed) (ohSecondary k y seed)).1.toNat,
        (xorChunk (ohSecondary k x seed) (ohSecondary k y seed)).2.toNat) ∈ maskSet ×ˢ maskSet := by
      simpa only [xorChunk, BitVec.toNat_xor] using
        project_eq_mask_cover (ohSecondary k x seed) (ohSecondary k y seed) he.2
    simpa only [secondary_difference_eq_body k seed x y hc hs, rawSecondaryMask] using hm
-- CHECKPOINT

/-- The literal two-word change count gives both nonzero ENH increments. -/
theorem enhChanges_two_words (x y : Block) (he : enhChanges x y = 2) :
    (lastChunk x).1 ≠ (lastChunk y).1 ∧ (lastChunk x).2 ≠ (lastChunk y).2 := by
  unfold enhChanges at he
  split_ifs at he <;> simp_all
-- CHECKPOINT

/-- The selected PH inputs inherit both changed coordinates and exactly the
minimum valuation from the last ENH chunk. -/
theorem single_ph_input_facts (x y : Block) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (he : enhChanges x y = 2)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) :
    (x.chunks.getD i (0,0)).1 ≠ (y.chunks.getD i (0,0)).1 ∧
    (x.chunks.getD i (0,0)).2 ≠ (y.chunks.getD i (0,0)).2 ∧
    min (wordValuation (x.chunks.getD i (0,0)).1 (y.chunks.getD i (0,0)).1)
      (wordValuation (x.chunks.getD i (0,0)).2 (y.chunks.getD i (0,0)).2) = enhValuation x y := by
  have hd := single_ph_checksum_difference x y hc hs i hi ho
  have h1 : (x.chunks.getD i (0,0)).1 ^^^ (y.chunks.getD i (0,0)).1 =
      (lastChunk x).1 ^^^ (lastChunk y).1 := congrArg Prod.fst hd
  have h2 : (x.chunks.getD i (0,0)).2 ^^^ (y.chunks.getD i (0,0)).2 =
      (lastChunk x).2 ^^^ (lastChunk y).2 := congrArg Prod.snd hd
  obtain ⟨hl1,hl2⟩ := enhChanges_two_words x y he
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [h, BitVec.xor_self] at h1
    exact hl1 (BitVec.xor_eq_zero_iff.mp h1.symm)
  · intro h
    rw [h, BitVec.xor_self] at h2
    exact hl2 (BitVec.xor_eq_zero_iff.mp h2.symm)
  · simp only [wordValuation, enhValuation, h1, h2]
-- CHECKPOINT

/-- The separate low PH and ENH differences retain the common zero prefix. -/
theorem single_ph_low_divisible (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hr : r = enhValuation x y) (hr64 : r ≤ 64) :
    2^r ∣ (blockPHDelta k x y i).1.toNat ∧
      2^r ∣ (blockENHDelta k seed x y).1.toNat := by
  have hr1 : r ≤ padicValNat 2 ((lastChunk x).1 ^^^ (lastChunk y).1).toNat :=
    hr ▸ min_le_left _ _
  have hr2 : r ≤ padicValNat 2 ((lastChunk x).2 ^^^ (lastChunk y).2).toNat :=
    hr ▸ min_le_right _ _
  have h1 : 2^r ∣ ((lastChunk x).1 ^^^ (lastChunk y).1).toNat :=
    (pow_dvd_pow 2 hr1).trans pow_padicValNat_dvd
  have h2 : 2^r ∣ ((lastChunk x).2 ^^^ (lastChunk y).2).toNat :=
    (pow_dvd_pow 2 hr2).trans pow_padicValNat_dvd
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
      (ph_low_prefix _ _ _ r hr64 hP1 hP2),
    (word_prefix_eq_iff_xor_dvd _ _ r).mp
      (enh_low_prefix _ _ _ _ _ r hr64 h1 h2)⟩
-- CHECKPOINT

/-- Both observed low masks lie in D intersect 2^r Z. -/
theorem single_ph_joint_low_masks (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hr : r = enhValuation x y) (hr64 : r ≤ 64)
    (he : jointEvent seed x y k) :
    (rawPrimaryMask k seed x y).1.toNat ∈ valuationMasks r ∧
      (rawSecondaryMask k seed x y).1.toNat ∈ valuationMasks r := by
  obtain ⟨hp,he'⟩ := single_ph_low_divisible k seed x y hc hs i hi ho r hr hr64
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
      phShuffleLane_prefix_zero _ r hr64 _ hp0, he0, Nat.xor_self]
-- CHECKPOINT

/-- PROOF2 reduction (8) on the actual block compressor: at r ≥ 4,
a joint projected collision forces both separate low differences to zero. -/
theorem single_ph_joint_low_zero (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hr : r = enhValuation x y) (hr4 : 4 ≤ r) (hr64 : r ≤ 64)
    (he : jointEvent seed x y k) :
    (blockPHDelta k x y i).1 = 0 ∧ (blockENHDelta k seed x y).1 = 0 := by
  obtain ⟨hp,he'⟩ := single_ph_low_divisible k seed x y hc hs i hi ho r hr hr64
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

/-- Two raw low masks force the exact independent PH and ENH targets
appearing in the low ledger. -/
theorem single_ph_low_targets (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) (u v : ℕ)
    (hu : (rawPrimaryMask k seed x y).1.toNat = u)
    (hv : (rawSecondaryMask k seed x y).1.toNat = v) :
    (blockPHDelta k x y i).1 = phenhPHMask (x.chunks.length-(i+1)) u v ∧
    (blockENHDelta k seed x y).1 = BitVec.ofNat 64 (phenhENHMask (x.chunks.length-(i+1)) u v) := by
  have ha := single_ph_raw_algebra k seed x y hc i hi ho
  have hword (a : Word) (b : ℕ) (h : a.toNat = b) : a = BitVec.ofNat 64 b := by
    rw [← h]
    simp
  have hpu := hword _ _ hu
  have hsv := hword _ _ hv
  rw [ha.1] at hpu
  rw [ha.2] at hsv
  have ht := shuffler_elimination_explicit (x.chunks.length-(i+1)) (by omega)
    (blockPHDelta k x y i).1 (blockENHDelta k seed x y).1
    (BitVec.ofNat 64 u) (BitVec.ofNat 64 v) hpu hsv
  refine ⟨ht.1, ?_⟩
  simpa only [phenhENHMask, phenhPHMask, BitVec.ofNat_toNat] using ht.2
-- CHECKPOINT

/-- The same exact inversion for the high raw masks. -/
theorem single_ph_high_targets (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) (u v : ℕ)
    (hu : (rawPrimaryMask k seed x y).2.toNat = u)
    (hv : (rawSecondaryMask k seed x y).2.toNat = v) :
    (blockPHDelta k x y i).2 = phenhPHMask (x.chunks.length-(i+1)) u v ∧
    (blockENHDelta k seed x y).2 = BitVec.ofNat 64 (phenhENHMask (x.chunks.length-(i+1)) u v) := by
  have ha := single_ph_raw_algebra k seed x y hc i hi ho
  have hword (a : Word) (b : ℕ) (h : a.toNat = b) : a = BitVec.ofNat 64 b := by
    rw [← h]
    simp
  have hpu := hword _ _ hu
  have hsv := hword _ _ hv
  rw [ha.1] at hpu
  rw [ha.2] at hsv
  have ht := shuffler_elimination_explicit (x.chunks.length-(i+1)) (by omega)
    (blockPHDelta k x y i).2 (blockENHDelta k seed x y).2
    (BitVec.ofNat 64 u) (BitVec.ofNat 64 v) hpu hsv
  refine ⟨ht.1, ?_⟩
  simpa only [phenhENHMask, phenhPHMask, BitVec.ofNat_toNat] using ht.2
-- CHECKPOINT

/-- The first 32 key words determine both raw masks; changing either
of the two twisting words leaves those masks unchanged. -/
theorem raw_masks_update_twist (K : Fin 17 → Chunk) (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16) (v : Chunk) :
    rawPrimaryMask (keyPairsEquiv.symm (Function.update K 16 v)) seed x y =
      rawPrimaryMask (keyPairsEquiv.symm K) seed x y ∧
    rawSecondaryMask (keyPairsEquiv.symm (Function.update K 16 v)) seed x y =
      rawSecondaryMask (keyPairsEquiv.symm K) seed x y := by
  simp only [rawPrimaryMask, rawSecondaryMask, oh, secondaryBody,
    mixed_update_later K x seed 16 hx v, mixed_update_later K y seed 16 hy v,
    and_self]
-- CHECKPOINT

end ProvenHashes.UMASH
