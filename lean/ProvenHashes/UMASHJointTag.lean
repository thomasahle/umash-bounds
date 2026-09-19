import ProvenHashes.UMASHSecondaryTag
import ProvenHashes.UMASHTagSharp
import ProvenHashes.UMASHTwistWeights

/-! Joint tag-only conditioning, using the primary tag bound from PROOF2
and the independent twisting words from PROOF5. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet

theorem mask_bit_set_prefix_card_gap (n e j : ℕ) (hj : j ≤ n) :
    (maskBitSet n e).card ≤ (maskBitSet j e).card+(n-j) := by
  induction n with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp
  | succ n ih =>
    by_cases h : j = n+1
    · subst j; simp
    · have hjn : j ≤ n := by omega
      have hi := ih hjn
      rw [mask_bit_set_succ_card]
      split <;> omega
-- CHECKPOINT

theorem twist_high_weight_dense_tag (e : ℕ) (hm : e ∈ maskSet)
    (hh : 54 ≤ (maskBitSet 64 e).card) :
    twistHighWeight e ≤ (524296:ℚ≥0)/q := by
  have hp : ∀ j ∈ Finset.range 64, 2^(j-(maskBitSet j e).card) ≤ (1024:ℕ) := by
    intro j hj
    have hj64 : j ≤ 64 := (Finset.mem_range.mp hj).le
    have hc := mask_bit_set_prefix_card_gap 64 e j hj64
    have hd : j-(maskBitSet j e).card ≤ 10 := by omega
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hd)
  have hs : twistHighFactorNumerator e ≤ 65537 := by
    unfold twistHighFactorNumerator
    have h := Finset.sum_le_sum hp
    simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul] using Nat.add_le_add_left h 1
  have hw : twistHighWeightNumerator e ≤ 524296 := by
    apply (min_le_right _ _).trans
    exact (Nat.mul_le_mul (maskSet_patterns_le_eight e hm) hs)
  rw [twistHighWeight_eq_numerator]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hw) (by positivity)
-- CHECKPOINT

theorem primary_tag_body_high_weight (k : OHKey) (seed : Word) (x y : Block)
    (hx : x.chunks ≠ []) (hsame : x.chunks = y.chunks)
    (hne : blockTag seed x ≠ blockTag seed y) (he : primaryEvent seed x y k) :
    twistHighWeight ((secondaryBody k x seed).2 ^^^ (secondaryBody k y seed).2).toNat ≤
      (524296:ℚ≥0)/q := by
  let xs := x.chunks.dropLast
  have hxs : x.chunks = xs ++ [lastChunk x] := block_chunks_split x hx
  have hys : y.chunks = xs ++ [lastChunk x] := hsame.symm.trans hxs
  let key := keyPair k xs.length
  let data := lastChunk x
  let H : Word := BitVec.ofNat 64 ((data.1+key.1).toNat*(data.2+key.2).toNat/q)
  have hbody : ((secondaryBody k x seed).2 ^^^ (secondaryBody k y seed).2) =
      (H+blockTag seed x) ^^^ (H+blockTag seed y) := by
    rw [secondaryBody_append_last k x seed xs (lastChunk x) hxs,
      secondaryBody_append_last k y seed xs (lastChunk x) hys]
    simp only [xorChunk, enh_high_as_word]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [H, data, key, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  have ho : ((oh k x seed).2 ^^^ (oh k y seed).2) =
      (H+blockTag seed x) ^^^ (H+blockTag seed y) := by
    rw [oh_append_last k x seed xs (lastChunk x) hxs,
      oh_append_last k y seed xs (lastChunk x) hys]
    simp only [xorChunk, enh_high_as_word]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [H, data, key, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  have hm : ((H+blockTag seed x) ^^^ (H+blockTag seed y)).toNat ∈ maskSet := by
    rw [← ho, BitVec.toNat_xor]
    exact (Finset.mem_product.mp (project_eq_mask_cover (oh k x seed) (oh k y seed) he)).2
  rw [hbody]
  exact twist_high_weight_dense_tag _ hm
    (tag_mask_popcount_ge54 H _ _ hne (blockTag_common_high seed x y) hm)
-- CHECKPOINT

theorem joint_tag_only_bound : TagOnlyBound := by
  intro seed x y hx hy hsame hne
  have hxl : 0 < x.chunks.length ∧ x.chunks.length ≤ 16 := by
    rcases hx with ⟨_,_,h⟩; omega
  have hyl : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
  have hc : sameCount x y := congrArg List.length hsame
  have hsum : dataChecksum x = dataChecksum y := by simp only [dataChecksum, hsame]
  let E := fun K : Fin 17 → Chunk => primaryEvent seed x y (keyPairsEquiv.symm K)
  let F := fun K : Fin 17 → Chunk => project (ohSecondary (keyPairsEquiv.symm K) x seed) =
    project (ohSecondary (keyPairsEquiv.symm K) y seed)
  have hE (K : Fin 17 → Chunk) (v : Chunk) : E (Function.update K 16 v) ↔ E K := by
    dsimp only [E, primaryEvent, oh]
    rw [mixed_update_later K x seed 16 hxl.2 v, mixed_update_later K y seed 16 hyl v]
  have hs (K : Fin 17 → Chunk) (hK : E K) :
      uniformProb (fun v => F (Function.update K 16 v)) ≤ (524296:ℚ≥0)/q := by
    have hm := primary_tag_body_high_weight (keyPairsEquiv.symm K) seed x y
      (List.ne_nil_of_length_pos hxl.1) hsame hne hK
    apply (probability_mono ?_).trans
      ((secondary_twist_high_weight K seed x y hxl.2 hyl hc hsum).trans hm)
    intro v hv
    have h := congrArg (fun z : Field × Field => z.2.val) hv
    simpa only [project, ZMod.val_natCast] using h
  have h := probability_and_update_event_le E F 16 ((524296:ℚ≥0)/q) hE hs
  have hequiv : uniformProb E = uniformProb (primaryEvent seed x y) :=
    uniformProb_equiv keyPairsEquiv.symm _
  have hjoint : uniformProb (fun K => E K ∧ F K) = uniformProb (jointEvent seed x y) :=
    uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)
  rw [hequiv, hjoint] at h
  calc
    _ ≤ uniformProb (primaryEvent seed x y)*((524296:ℚ≥0)/q) := h
    _ ≤ ((1:ℚ≥0)/(8*q))*((524296:ℚ≥0)/q) :=
      mul_le_mul_of_nonneg_right (primary_tag_only_sharp seed x y hx hy hsame hne).le
        (by positivity)
    _ < _ := by apply NNRat.coe_lt_coe.mp; norm_num [q]
-- CHECKPOINT

end ProvenHashes.UMASH
