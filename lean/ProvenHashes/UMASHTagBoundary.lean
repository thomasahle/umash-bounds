import ProvenHashes.UMASHHighProduct
import ProvenHashes.UMASHBlockENH

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype maskSet

theorem blockTag_common_high (seed : Word) (x y : Block) :
    (blockTag seed x).toNat/256 = (blockTag seed y).toNat/256 := by
  have hval (b : Block) : (BitVec.ofNat 64 (b.byteSize%256)).toNat = b.byteSize%256 := by
    apply Nat.mod_eq_of_lt
    have := Nat.mod_lt b.byteSize (by decide : 0 < 256)
    norm_num
    omega
  simp only [blockTag, BitVec.toNat_xor, hval]
  change (seed.toNat ^^^ (x.byteSize%256))/2^8 = (seed.toNat ^^^ (y.byteSize%256))/2^8
  rw [Nat.xor_div_two_pow, Nat.xor_div_two_pow]
  have hx : x.byteSize%256/2^8 = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
  have hy : y.byteSize%256/2^8 = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
  rw [hx, hy]
-- CHECKPOINT

theorem masked_word_projection_top_ne (M U V : Word) (hne : U ≠ V)
    (he : (M ^^^ U).toNat%p = (M ^^^ V).toNat%p) :
    U.toNat/2^60 ≠ V.toNat/2^60 := by
  have hm : U.toNat ^^^ V.toNat ∈ maskSet := by
    have h := congruent_xor_mem_maskSet _ _ (M ^^^ U).isLt (M ^^^ V).isLt he
    have hx : (M ^^^ U) ^^^ (M ^^^ V) = U ^^^ V := by
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
    rw [← BitVec.toNat_xor, hx, BitVec.toNat_xor] at h
    exact h
  have hn : U.toNat ^^^ V.toNat ≠ 0 := by
    intro hz
    have hw : U ^^^ V = 0 := by
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_xor, BitVec.toNat_zero] using hz
    exact hne (BitVec.xor_eq_zero_iff.mp hw)
  have hl := maskSet_nonzero_large _ hm hn
  intro hsame
  have hz : (U.toNat ^^^ V.toNat)/2^60 = 0 := by
    rw [Nat.xor_div_two_pow, hsame, Nat.xor_self]
  norm_num at hz hl
  omega
-- CHECKPOINT

/-- A 256-word interval before each of the sixteen top-nibble boundaries. -/
def tagBoundaryTargets (tag : Word) : Finset Word :=
  ((Finset.range 16) ×ˢ (Finset.range 256)).image
    (fun cr => BitVec.ofNat 64 (cr.1*2^60+(2^60-256)+cr.2)-tag)

theorem tagBoundaryTargets_card (tag : Word) : (tagBoundaryTargets tag).card ≤ 4096 := by
  exact Finset.card_image_le.trans_eq (by rw [Finset.card_product]; norm_num)
-- CHECKPOINT

theorem tag_boundary_cover (H tag tag' : Word)
    (horder : tag.toNat ≤ tag'.toNat) (hcommon : tag.toNat/256 = tag'.toNat/256)
    (hcross : (H+tag).toNat/2^60 ≠ (H+tag').toNat/2^60) :
    H ∈ tagBoundaryTargets tag := by
  let X := (H+tag).toNat
  have hX : X < q := (H+tag).isLt
  have hr : 2^60-256 ≤ X%2^60 := by
    dsimp only [X]
    rw [BitVec.toNat_add, BitVec.toNat_add] at hcross
    rw [BitVec.toNat_add]
    norm_num at hcross ⊢
    omega
  let c := X/2^60
  let d := X%2^60-(2^60-256)
  have hc : c < 16 := by dsimp [c]; norm_num [q] at hX ⊢; omega
  have hd : d < 256 := by
    have hmod := Nat.mod_lt X (by norm_num : 0 < 2^60)
    dsimp [d]
    omega
  have hval : c*2^60+(2^60-256)+d = X := by
    have hmod := Nat.mod_add_div X (2^60)
    dsimp [c, d]
    omega
  apply Finset.mem_image.mpr
  refine ⟨(c,d), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hc, Finset.mem_range.mpr hd⟩, ?_⟩
  have hw : BitVec.ofNat 64 (c*2^60+(2^60-256)+d) = H+tag := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hval, Nat.mod_eq_of_lt (H+tag).isLt]
  rw [hw, add_sub_cancel_right]
-- CHECKPOINT

theorem enh_high_as_word (key data : Chunk) (tag : Word) :
    (enh key data tag).2 =
      (BitVec.ofNat 64 ((data.1+key.1).toNat*(data.2+key.2).toNat/q)+tag) ^^^
        BitVec.ofNat 64 ((data.1+key.1).toNat*(data.2+key.2).toNat%q) := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg Prod.snd (enh_toNat key data tag)
  dsimp only at h
  rw [h]
  simp only [BitVec.toNat_xor, BitVec.toNat_add, BitVec.toNat_ofNat,
    q, Nat.mod_add_mod, Nat.mod_mod]
-- CHECKPOINT

end ProvenHashes.UMASH
