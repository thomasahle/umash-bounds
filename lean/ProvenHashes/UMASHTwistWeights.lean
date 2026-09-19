import ProvenHashes.UMASHPHWeights

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

def twistHighWeight (e : ℕ) : ℚ≥0 := min 1 ((maskPatterns e).card*twistHighFactor e)
def twistLowWeight (e : ℕ) : ℚ≥0 := min 1 ((maskPatterns e).card*twistLowFactor e)

/-- Projection after adding a common XOR noise word is a union over the
actual admissible patterns of the fixed output difference. -/
theorem common_xor_projection_probability {K : Type*} [Fintype K] [Nonempty K]
    (noise : K → Word) (M N : Word) (rate : ℚ≥0)
    (hpattern : ∀ z : ℕ, uniformProb (fun k =>
      (M ^^^ noise k).toNat &&& (M ^^^ N).toNat = z) ≤ rate) :
    uniformProb (fun k => (M ^^^ noise k).toNat%p = (N ^^^ noise k).toNat%p) ≤
      min 1 ((maskPatterns (M ^^^ N).toNat).card*rate) := by
  apply le_min (probability_le_one _)
  let T := maskPatterns (M ^^^ N).toNat
  let E (z : ℕ) (k : K) := (M ^^^ noise k).toNat &&& (M ^^^ N).toNat = z
  have hx (k : K) : (M ^^^ noise k) ^^^ (N ^^^ noise k) = M ^^^ N := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm,
      Bool.xor_comm, Bool.xor_self, Bool.xor_false, Bool.false_xor]
  have hcover (k : K) (hk : (M ^^^ noise k).toNat%p = (N ^^^ noise k).toNat%p) :
      ∃ z ∈ T, E z k := by
    refine ⟨(M ^^^ noise k).toNat &&& (M ^^^ N).toNat, ?_, rfl⟩
    have hh := congruent_pattern _ _ (M ^^^ noise k).isLt (N ^^^ noise k).isLt hk
    simpa only [← BitVec.toNat_xor, hx] using hh
  calc
    _ ≤ uniformProb (fun k => ∃ z ∈ T, E z k) := probability_mono hcover
    _ ≤ ∑ z ∈ T, uniformProb (E z) := probability_union_bound _ _
    _ ≤ ∑ _z ∈ T, rate := Finset.sum_le_sum (fun z _ => hpattern z)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
-- CHECKPOINT

/-- XOR translation by a fixed checksum preserves the two independent
uniform twisting words. -/
theorem checksum_translate_probability (checksum : Chunk) (E : Chunk → Prop) :
    uniformProb (fun k : Chunk => E (xorChunk checksum k)) = uniformProb E := by
  let equiv : Chunk ≃ Chunk :=
    { toFun := xorChunk checksum
      invFun := xorChunk checksum
      left_inv := by intro k; apply Prod.ext <;> simp [xorChunk, ← BitVec.xor_assoc]
      right_inv := by intro k; apply Prod.ext <;> simp [xorChunk, ← BitVec.xor_assoc] }
  exact uniformProb_equiv equiv E
-- CHECKPOINT

/-- A literal PH twisting product has the high pattern weight after every
original chunk key, and therefore the common checksum, has been fixed. -/
theorem twist_high_pattern_probability (checksum : Chunk) (offset : Word) (e z : ℕ) :
    uniformProb (fun k : Chunk => (offset ^^^ (ph k checksum).2).toNat &&& e = z) ≤
      twistHighFactor e := by
  simp only [ph]
  change uniformProb (fun k : Chunk =>
    (fun ab : Chunk => (offset ^^^ (split (clmul ab.1 ab.2)).2).toNat &&& e = z)
      (xorChunk checksum k)) ≤ _
  rw [checksum_translate_probability checksum
    (fun ab : Chunk => (offset ^^^ (split (clmul ab.1 ab.2)).2).toNat &&& e = z)]
  exact clmul_high_pattern_probability offset e z
-- CHECKPOINT

/-- The corresponding literal PH low pattern weight. -/
theorem twist_low_pattern_probability (checksum : Chunk) (offset : Word) (e z : ℕ) :
    uniformProb (fun k : Chunk => (offset ^^^ (ph k checksum).1).toNat &&& e = z) ≤
      twistLowFactor e := by
  simp only [ph]
  change uniformProb (fun k : Chunk =>
    (fun ab : Chunk => (offset ^^^ (split (clmul ab.1 ab.2)).1).toNat &&& e = z)
      (xorChunk checksum k)) ≤ _
  rw [checksum_translate_probability checksum
    (fun ab : Chunk => (offset ^^^ (split (clmul ab.1 ab.2)).1).toNat &&& e = z)]
  exact clmul_low_pattern_probability offset e z
-- CHECKPOINT

/-- PROOF2 Lemma 3.2, high lane, with both fixed offsets retained. -/
theorem twist_high_projection_probability (checksum : Chunk) (M N : Word) :
    uniformProb (fun k : Chunk =>
      (M ^^^ (ph k checksum).2).toNat%p = (N ^^^ (ph k checksum).2).toNat%p) ≤
      twistHighWeight (M ^^^ N).toNat := by
  exact common_xor_projection_probability (fun k => (ph k checksum).2) M N
    (twistHighFactor (M ^^^ N).toNat)
    (fun z => twist_high_pattern_probability checksum M (M ^^^ N).toNat z)
-- CHECKPOINT

/-- PROOF2 Lemma 3.2, low lane, with both fixed offsets retained. -/
theorem twist_low_projection_probability (checksum : Chunk) (M N : Word) :
    uniformProb (fun k : Chunk =>
      (M ^^^ (ph k checksum).1).toNat%p = (N ^^^ (ph k checksum).1).toNat%p) ≤
      twistLowWeight (M ^^^ N).toNat := by
  exact common_xor_projection_probability (fun k => (ph k checksum).1) M N
    (twistLowFactor (M ^^^ N).toNat)
    (fun z => twist_low_pattern_probability checksum M (M ^^^ N).toNat z)
-- CHECKPOINT

/-- The keyed checksum is the data checksum plus a length-dependent key sum. -/
theorem checksum_code_split (k : OHKey) (b : Block) :
    chunkCode (checksum k b) = chunkCode (dataChecksum b) +
      ∑ i : Fin b.chunks.length, chunkCode (keyPair k i.val) := by
  have hl : (b.chunks.mapIdx (fun i x => xorChunk x (keyPair k i))).map chunkCode =
      List.ofFn (fun i : Fin b.chunks.length => chunkCode (xorChunk b.chunks[i] (keyPair k i.val))) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  have hd : b.chunks.map chunkCode = List.ofFn (fun i : Fin b.chunks.length => chunkCode b.chunks[i]) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  rw [checksum, chunkCode_fold, chunkCode_zero, zero_add, hl, List.sum_ofFn]
  simp_rw [chunkCode_xor]
  rw [Finset.sum_add_distrib, dataChecksum, chunkCode_fold, chunkCode_zero, zero_add, hd, List.sum_ofFn]
-- CHECKPOINT

/-- Equal data checksums at equal chunk counts give literal equal keyed
checksums for every assignment of the original keys. -/
theorem checksum_eq_of_data_checksum (k : OHKey) (x y : Block)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y) :
    checksum k x = checksum k y := by
  apply chunkCode_injective
  rw [checksum_code_split, checksum_code_split, hs]
  change x.chunks.length = y.chunks.length at hc
  rw [hc]
-- CHECKPOINT

/-- Lemma 3.2 on the literal secondary high lane, conditional on all 32
original words. The final two twisting words remain independently uniform. -/
theorem secondary_twist_high_weight (K : Fin 17 → Chunk) (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y) :
    uniformProb (fun v : Chunk =>
      (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) x seed).2.toNat%p =
      (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) y seed).2.toNat%p) ≤
      twistHighWeight ((secondaryBody (keyPairsEquiv.symm K) x seed).2 ^^^
        (secondaryBody (keyPairsEquiv.symm K) y seed).2).toNat := by
  simp only [secondary_twist_slice K x seed hx, secondary_twist_slice K y seed hy,
    checksum_eq_of_data_checksum (keyPairsEquiv.symm K) x y hc hs, xorChunk]
  exact twist_high_projection_probability _ _ _
-- CHECKPOINT

/-- Lemma 3.2 on the literal secondary low lane, with exactly the same
conditioning on the original word keys. -/
theorem secondary_twist_low_weight (K : Fin 17 → Chunk) (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y) :
    uniformProb (fun v : Chunk =>
      (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) x seed).1.toNat%p =
      (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) y seed).1.toNat%p) ≤
      twistLowWeight ((secondaryBody (keyPairsEquiv.symm K) x seed).1 ^^^
        (secondaryBody (keyPairsEquiv.symm K) y seed).1).toNat := by
  simp only [secondary_twist_slice K x seed hx, secondary_twist_slice K y seed hy,
    checksum_eq_of_data_checksum (keyPairsEquiv.symm K) x y hc hs, xorChunk]
  exact twist_low_projection_probability _ _ _
-- CHECKPOINT

end ProvenHashes.UMASH
