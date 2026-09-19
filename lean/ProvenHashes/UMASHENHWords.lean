import ProvenHashes.UMASHENHFibre
import ProvenHashes.UMASHProduct

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

theorem widened_word_toNat (a : Word) : (a.zeroExtend 128).toNat = a.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (a.isLt.trans (by norm_num))
-- CHECKPOINT

theorem widened_product_toNat (a b : Word) :
    (a.zeroExtend 128 * b.zeroExtend 128).toNat = a.toNat*b.toNat := by
  rw [BitVec.toNat_mul, widened_word_toNat, widened_word_toNat]
  apply Nat.mod_eq_of_lt
  have h := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  norm_num only [Nat.reducePow] at h ⊢
  exact h
-- CHECKPOINT

theorem high_tag_toNat (tag : Word) :
    (tag.zeroExtend 128 <<< 64).toNat = tag.toNat*q := by
  rw [BitVec.toNat_shiftLeft, widened_word_toNat, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have ht := Nat.mul_lt_mul_of_pos_right tag.isLt (by positivity : 0 < 2^64)
  norm_num only [Nat.reducePow] at ht ⊢
  exact ht
-- CHECKPOINT

theorem tagged_split_low (x : Wide) (tag : Word) :
    (split (x + (tag.zeroExtend 128 <<< 64))).1.toNat = x.toNat % q := by
  simp only [split, BitVec.toNat_setWidth, BitVec.toNat_add, high_tag_toNat]
  change ((x.toNat+tag.toNat*q) % (q*q)) % q = _
  rw [Nat.mod_mul_left_mod]
  exact Nat.add_mul_mod_self_right _ _ _
-- CHECKPOINT

theorem tagged_split_high (x : Wide) (tag : Word) :
    (split (x + (tag.zeroExtend 128 <<< 64))).2.toNat =
      (x.toNat/q+tag.toNat) % q := by
  simp only [split, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_add, high_tag_toNat]
  change (((x.toNat+tag.toNat*q) % (q*q)) / q) % q = _
  rw [Nat.mod_mul_right_div_self, Nat.mod_mod,
    Nat.add_mul_div_right _ _ (by norm_num [q])]
-- CHECKPOINT

/-- Exact correspondence with the literal widened multiplication, high tag,
and triangular fold used in UMASHModel.enh. -/
theorem enh_toNat (key data : Chunk) (tag : Word) :
    ((enh key data tag).1.toNat, (enh key data tag).2.toNat) =
      (let A := (data.1+key.1).toNat
       let B := (data.2+key.2).toNat
       (A*B % q, ((A*B/q+tag.toNat)%q) ^^^ (A*B%q))) := by
  simp only [enh, BitVec.toNat_xor, tagged_split_low, tagged_split_high,
    widened_product_toNat]
-- CHECKPOINT

theorem masked_enh_high_toNat (key data : Chunk) (tag M : Word) :
    (M ^^^ (enh key data tag).2).toNat =
      enhHighNat q (data.1+key.1).toNat (data.2+key.2).toNat tag.toNat M.toNat := by
  have h := congrArg Prod.snd (enh_toNat key data tag)
  dsimp only at h
  simp only [BitVec.toNat_xor, h, enhHighNat]
  rw [Nat.xor_comm (((data.1+key.1).toNat*(data.2+key.2).toNat/q+tag.toNat)%q),
    Nat.xor_assoc]
-- CHECKPOINT

end ProvenHashes.UMASH
