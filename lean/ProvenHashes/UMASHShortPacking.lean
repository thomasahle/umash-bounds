import ProvenHashes.UMASHShortMixer
import ProvenHashes.ClassicBytes

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

theorem loadLE_eq_bytesNat (m : Message) : loadLE m = Classic.bytesNat m := by
  induction m with
  | nil => rfl
  | cons b bs ih =>
    change b.val + 256*loadLE bs = b.val + 256*Classic.bytesNat bs
    rw [ih]
-- CHECKPOINT

theorem loadLE_lt_of_length (m : Message) (n : ℕ) (hm : m.length ≤ n) :
    loadLE m < 256^n := by
  rw [loadLE_eq_bytesNat]
  exact (Classic.bytesNat_lt m).trans_le (Nat.pow_le_pow_right (by omega) hm)
-- CHECKPOINT

def shortLow (m : Message) : ℕ :=
  if 4 ≤ m.length then loadLE (m.take 4)
  else if m.length%2 = 1 then loadLE (m.take 1) else 0

def shortHigh (m : Message) : ℕ :=
  if 4 ≤ m.length then loadLE (m.drop (m.length-4))
  else if 2 ≤ m.length then loadLE (m.drop (m.length-2)) else 0

theorem shortLow_lt (m : Message) : shortLow m < 2^32 := by
  unfold shortLow
  split_ifs
  · exact loadLE_lt_of_length (m.take 4) 4 (by simp)
  · exact (loadLE_lt_of_length (m.take 1) 1 (by simp)).trans_le (by norm_num)
  · norm_num
-- CHECKPOINT

theorem shortHigh_lt (m : Message) : shortHigh m < 2^32 := by
  unfold shortHigh
  split_ifs
  · exact loadLE_lt_of_length (m.drop (m.length-4)) 4 (by simp; omega)
  · exact (loadLE_lt_of_length (m.drop (m.length-2)) 2 (by simp; omega)).trans_le
      (by norm_num)
  · norm_num
-- CHECKPOINT

theorem shortPack_toNat (m : Message) :
    (shortPack m).toNat = shortHigh m*2^32 + (shortHigh m+shortLow m)%2^32 := by
  change (BitVec.ofNat 64 (shortHigh m*2^32 + (shortHigh m+shortLow m)%2^32)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have hh := shortHigh_lt m
  have hr := Nat.mod_lt (shortHigh m+shortLow m) (show 0 < 2^32 by norm_num)
  norm_num only [Nat.reducePow] at *
  omega
-- CHECKPOINT

theorem shortPack_components (x y : Message) (h : shortPack x = shortPack y) :
    shortLow x = shortLow y ∧ shortHigh x = shortHigh y := by
  have he := congrArg BitVec.toNat h
  rw [shortPack_toNat, shortPack_toNat] at he
  have hxl := shortLow_lt x
  have hyl := shortLow_lt y
  have hxh := shortHigh_lt x
  have hyh := shortHigh_lt y
  norm_num only [Nat.reducePow] at *
  omega
-- CHECKPOINT

/-- Overlapping prefix and suffix cover a list whenever its length is at most
twice their width. This also records the reconstruction for lengths 4 through 8. -/
theorem list_eq_of_overlapping_ends {α : Type*} (x y : List α) (n : ℕ)
    (hl : x.length = y.length) (hsize : x.length ≤ 2*n)
    (ht : x.take n = y.take n)
    (hd : x.drop (x.length-n) = y.drop (y.length-n)) : x = y := by
  have hx : (x.length-n)+(n-(x.length-n)) = n := by omega
  have he := congrArg (fun l : List α => l.drop (n-(x.length-n))) hd
  simp only [List.drop_drop, ← hl, hx] at he
  rw [← List.take_append_drop n x, ← List.take_append_drop n y, ht, he]
-- CHECKPOINT

theorem shortPack_injective_length (x y : Message) (hx : x.length ≤ 8)
    (hl : x.length = y.length) (he : shortPack x = shortPack y) : x = y := by
  obtain ⟨hlo,hhi⟩ := shortPack_components x y he
  by_cases h4 : 4 ≤ x.length
  · have hy4 : 4 ≤ y.length := by omega
    simp only [shortLow, shortHigh, h4, hy4, ↓reduceIte] at hlo hhi
    apply list_eq_of_overlapping_ends x y 4 hl hx
    · apply Classic.bytesNat_inj_length (by simp [hl])
      simpa only [← loadLE_eq_bytesNat] using hlo
    · apply Classic.bytesNat_inj_length (by simp [hl])
      simpa only [← loadLE_eq_bytesNat] using hhi
  · have hx4 : x.length < 4 := by omega
    interval_cases hlen : x.length
    · have hy0 : y.length = 0 := by omega
      exact (List.length_eq_zero_iff.mp hlen).trans (List.length_eq_zero_iff.mp hy0).symm
    · have hy1 : y.length = 1 := by omega
      simp only [shortLow, hlen, hy1, Nat.reduceLeDiff, Nat.reduceMod,
        ↓reduceIte, List.take_of_length_le (by omega : x.length ≤ 1),
        List.take_of_length_le (by omega : y.length ≤ 1)] at hlo
      apply Classic.bytesNat_inj_length (hlen.trans hl)
      simpa only [← loadLE_eq_bytesNat] using hlo
    · have hy2 : y.length = 2 := by omega
      simp only [shortHigh, hlen, hy2, Nat.reduceLeDiff, Nat.reduceSub,
        ↓reduceIte, List.drop_zero] at hhi
      apply Classic.bytesNat_inj_length (hlen.trans hl)
      simpa only [← loadLE_eq_bytesNat] using hhi
    · have hy3 : y.length = 3 := by omega
      simp only [shortLow, shortHigh, hlen, hy3, Nat.reduceLeDiff, Nat.reduceMod,
        Nat.reduceSub, ↓reduceIte] at hlo hhi
      have ht : x.take 1 = y.take 1 := Classic.bytesNat_inj_length (by simp [hlen, hy3])
        (by simpa only [← loadLE_eq_bytesNat] using hlo)
      have hd : x.drop 1 = y.drop 1 := Classic.bytesNat_inj_length (by simp [hlen, hy3])
        (by simpa only [← loadLE_eq_bytesNat] using hhi)
      rw [← List.take_append_drop 1 x, ← List.take_append_drop 1 y, ht, hd]
-- CHECKPOINT

theorem short_equal_length_injective : ShortEqualLengthInjective := by
  intro seed k x y hx hl h
  rw [shortHash_eq_mixer, shortHash_eq_mixer, ← hl] at h
  have hp := (BitVec.xor_left_inj (seed + keyWord k x.length)).mp
    (shortFinish_injective h)
  exact shortPack_injective_length x y hx hl (shortPrepare_injective hp)
-- CHECKPOINT

end ProvenHashes.UMASH
