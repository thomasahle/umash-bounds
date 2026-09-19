import ProvenHashes.UMASHTagBoundary
import ProvenHashes.UMASHLedgerTables

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The highest selected bit cannot be canceled by all the lower selected bits. -/
theorem signed_submask_gap (k m t : ℕ) (hl : 2^k ≤ m) (hu : m < 2^(k+1))
    (ht : t &&& m = t) :
    2*(t:ℤ)-m ≤ (m:ℤ)-(2:ℤ)^(k+1) ∨
      (2:ℤ)^(k+1)-m ≤ 2*(t:ℤ)-m := by
  have hpN : (2:ℕ)^(k+1) = 2*2^k := by rw [pow_succ]; omega
  have hpZ : (2:ℤ)^(k+1) = 2*(2^k:ℕ) := by exact_mod_cast hpN
  rw [hpN] at hu
  rw [hpZ]
  by_cases htop : 2^k ≤ t
  · right
    omega
  · left
    have htlt : t < 2^k := by omega
    have hm : m%2^k = m-2^k := by
      rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt (by omega : m-2^k < 2^k)]
    have hmod := congrArg (fun a : ℕ => a%2^k) ht
    dsimp only at hmod
    rw [Nat.and_mod_two_pow, Nat.mod_eq_of_lt htlt] at hmod
    have htle : t ≤ m%2^k := by rw [← hmod]; exact Nat.and_le_right
    rw [hm] at htle
    omega
-- CHECKPOINT

/-- Both the ordinary and circular distances dominate the signed-mask gap. -/
theorem close_word_xor_gap (U V : Word) (k : ℕ)
    (hl : 2^k ≤ (U ^^^ V).toNat) (hu : (U ^^^ V).toNat < 2^(k+1))
    (hk : k < 64)
    (hclose : (-(255:ℤ) ≤ (U.toNat:ℤ)-V.toNat ∧ (U.toNat:ℤ)-V.toNat ≤ 255) ∨
      (q:ℤ)-255 ≤ (U.toNat:ℤ)-V.toNat ∨
        (U.toNat:ℤ)-V.toNat ≤ 255-(q:ℤ)) :
    2^(k+1)-(U ^^^ V).toNat ≤ 255 := by
  let m := (U ^^^ V).toNat
  let t := U.toNat &&& m
  have ht : t &&& m = t := by dsimp [t]; rw [Nat.and_assoc, Nat.and_self]
  have htm : t ≤ m := Nat.and_le_right
  have hd : (U.toNat:ℤ)-V.toNat = 2*(t:ℤ)-m := by
    simpa only [m, t, BitVec.toNat_xor] using xor_signed_difference U.toNat V.toNat
  have hg := signed_submask_gap k m t hl hu ht
  have hp : 2^(k+1) ≤ q := Nat.pow_le_pow_right (by decide) (by omega)
  have hc : ((2:ℤ)^(k+1):ℤ) = (2^(k+1):ℕ) := by norm_cast
  rw [hc] at hg
  change 2^(k+1)-m ≤ 255
  rcases hclose with h | h | h <;> omega
-- CHECKPOINT

/-- Tags sharing their upper 56 bits stay within circular distance 255
after addition of the same high product word. -/
theorem tag_words_close (H tag tag' : Word)
    (hcommon : tag.toNat/256 = tag'.toNat/256) :
    (-(255:ℤ) ≤ ((H+tag).toNat:ℤ)-(H+tag').toNat ∧
        ((H+tag).toNat:ℤ)-(H+tag').toNat ≤ 255) ∨
      (q:ℤ)-255 ≤ ((H+tag).toNat:ℤ)-(H+tag').toNat ∨
        ((H+tag).toNat:ℤ)-(H+tag').toNat ≤ 255-(q:ℤ) := by
  have hH := H.isLt
  have ht := tag.isLt
  have ht' := tag'.isLt
  simp only [BitVec.toNat_add]
  norm_num [q] at hH ht ht' ⊢
  omega
-- CHECKPOINT

set_option maxHeartbeats 0

/-- The exact mask census supplies the eight-pattern bound and the only
gap-versus-popcount implication needed by the tag-only argument. -/
theorem tag_mask_dense_certificate :
    (sortedUnique maskList3125).all (fun m => decide (
      (maskPatterns m).card ≤ 8 ∧
      (m = 0 ∨ 54 ≤ ledgerPopcount m 64 ∨ 256 ≤ 2^(m.log2+1)-m))) = true := by
  decide +kernel
-- CHECKPOINT

set_option maxHeartbeats 2000000

theorem maskSet_patterns_le_eight (m : ℕ) (hm : m ∈ maskSet) :
    (maskPatterns m).card ≤ 8 := by
  have hmem : m ∈ sortedUnique maskList3125 := by
    rw [← List.mem_toFinset, sortedUnique_toFinset]
    rw [maskSet_eq_fastCertificate, fastMaskCertificate, fastFinset_eq] at hm
    exact hm
  exact (of_decide_eq_true ((List.all_eq_true.mp tag_mask_dense_certificate) m hmem)).1
-- CHECKPOINT

/-- The 54-bit restriction for the literal tag pair, uniformly in H. -/
theorem tag_mask_popcount_ge54 (H tag tag' : Word)
    (hne : tag ≠ tag') (hcommon : tag.toNat/256 = tag'.toNat/256)
    (hm : ((H+tag) ^^^ (H+tag')).toNat ∈ maskSet) :
    54 ≤ (maskBitSet 64 ((H+tag) ^^^ (H+tag')).toNat).card := by
  let m := ((H+tag) ^^^ (H+tag')).toNat
  have hm0 : m ≠ 0 := by
    intro h
    have he : (H+tag) ^^^ (H+tag') = 0 := BitVec.eq_of_toNat_eq h
    exact hne (add_left_cancel (BitVec.xor_eq_zero_iff.mp he))
  have hmem : m ∈ sortedUnique maskList3125 := by
    rw [← List.mem_toFinset, sortedUnique_toFinset]
    rw [maskSet_eq_fastCertificate, fastMaskCertificate, fastFinset_eq] at hm
    exact hm
  have hc := (of_decide_eq_true ((List.all_eq_true.mp tag_mask_dense_certificate) m hmem)).2
  have hl : 2^m.log2 ≤ m := (Nat.le_log2 hm0).mp le_rfl
  have hu : m < 2^(m.log2+1) := (Nat.log2_lt hm0).mp (by omega)
  have hk : m.log2 < 64 := (Nat.log2_lt hm0).mpr ((H+tag) ^^^ (H+tag')).isLt
  have hg := close_word_xor_gap (H+tag) (H+tag') m.log2 hl hu hk
    (tag_words_close H tag tag' hcommon)
  rw [ledgerPopcount_correct] at hc
  rcases hc with h | h | h
  · exact (hm0 h).elim
  · exact h
  · omega
-- CHECKPOINT

end ProvenHashes.UMASH
