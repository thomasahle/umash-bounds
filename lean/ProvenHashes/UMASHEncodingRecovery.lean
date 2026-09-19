import ProvenHashes.UMASHEncoding
import ProvenHashes.UMASHShortPacking

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

theorem readWord_injective_length (x y : Message) (hx : x.length ≤ 8)
    (hl : x.length = y.length) (he : readWord x = readWord y) : x = y := by
  have hxl : loadLE x < 2^64 := loadLE_lt_of_length x 8 hx
  have hyl : loadLE y < 2^64 := loadLE_lt_of_length y 8 (by omega)
  have hv := congrArg BitVec.toNat he
  simp only [readWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] at hv
  apply Classic.bytesNat_inj_length hl
  simpa only [← loadLE_eq_bytesNat] using hv
-- CHECKPOINT

theorem encodeBlock_eq_of_encode_eq (x y : Message) (he : encode x = encode y)
    (i : ℕ) (hi : i < (x.length+255)/256) : encodeBlock x i = encodeBlock y i := by
  have hget := List.getElem_of_eq he (i := i) (by simpa only [encode_length] using hi)
  simpa only [encode, List.getElem_map, List.getElem_range] using hget
-- CHECKPOINT

theorem encode_recovers_length (x y : Message) (hx : 0 < x.length) (hy : 0 < y.length)
    (he : encode x = encode y) : x.length = y.length := by
  have hn := congrArg List.length he
  simp only [encode_length] at hn
  let i := (x.length+255)/256-1
  have hi : i < (x.length+255)/256 := by dsimp [i]; omega
  have hb := congrArg Block.byteSize (encodeBlock_eq_of_encode_eq x y he i hi)
  simp only [encodeBlock] at hb
  dsimp only [i] at hb
  omega
-- CHECKPOINT

theorem chunkAt_eq_of_encode_eq (x y : Message) (he : encode x = encode y)
    (i : ℕ) (hi : i < (x.length+15)/16) : chunkAt x i = chunkAt y i := by
  have hb : i/16 < (x.length+255)/256 := by omega
  have hblk := congrArg Block.chunks (encodeBlock_eq_of_encode_eq x y he (i/16) hb)
  have hj : i%16 < ((encodeBlock x (i/16)).chunks).length := by
    simp only [encodeBlock, List.length_map, List.length_range]
    omega
  have hget := List.getElem_of_eq hblk (i := i%16) hj
  simp only [encodeBlock, List.getElem_map, List.getElem_range] at hget
  have hind : 16*(i/16)+i%16 = i := by omega
  simpa only [hind] using hget
-- CHECKPOINT

theorem byte_eq_of_equal_slice (x y : Message) (s n i : ℕ)
    (hx : i < x.length) (hy : i < y.length) (hsi : s ≤ i) (hin : i < s+n)
    (he : (x.drop s).take n = (y.drop s).take n) : x[i] = y[i] := by
  have hi : i-s < ((x.drop s).take n).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have hget := List.getElem_of_eq he (i := i-s) hi
  simpa only [List.getElem_take, List.getElem_drop, Nat.add_sub_of_le hsi] using hget
-- CHECKPOINT

theorem chunkAt_recovers_message (x y : Message) (hx : 8 < x.length)
    (hl : x.length = y.length)
    (he : ∀ i, i < (x.length+15)/16 → chunkAt x i = chunkAt y i) : x = y := by
  by_cases hs : x.length < 16
  · have hsy : y.length < 16 := by omega
    have hchunk := he 0 (by omega)
    simp only [chunkAt, hs, hsy, ↓reduceIte] at hchunk
    apply list_eq_of_overlapping_ends x y 8 hl (by omega)
    · exact readWord_injective_length _ _ (by simp) (by simp [hl]) (congrArg Prod.fst hchunk)
    · exact readWord_injective_length _ _ (by simp; omega) (by simp [hl]) (congrArg Prod.snd hchunk)
  · have hsy : ¬ y.length < 16 := by omega
    apply List.ext_getElem hl
    intro i hix hiy
    let j := i/16
    let s := min (16*j) (x.length-16)
    have hj : j < (x.length+15)/16 := by dsimp [j]; omega
    have hsle : s ≤ i := by dsimp [s, j]; omega
    have his : i < s+16 := by dsimp [s, j]; omega
    have hsend : s+16 ≤ x.length := by dsimp [s]; omega
    have hchunk := he j hj
    simp only [chunkAt, hs, hsy, ↓reduceIte, ← hl] at hchunk
    change (readWord ((x.drop s).take 8), readWord ((x.drop (s+8)).take 8)) =
      (readWord ((y.drop s).take 8), readWord ((y.drop (s+8)).take 8)) at hchunk
    by_cases hleft : i < s+8
    · have hslice : (x.drop s).take 8 = (y.drop s).take 8 :=
        readWord_injective_length _ _ (by simp) (by simp [hl]) (congrArg Prod.fst hchunk)
      exact byte_eq_of_equal_slice x y s 8 i hix hiy hsle hleft hslice
    · have hslice : (x.drop (s+8)).take 8 = (y.drop (s+8)).take 8 :=
        readWord_injective_length _ _ (by simp) (by simp [hl]) (congrArg Prod.snd hchunk)
      exact byte_eq_of_equal_slice x y (s+8) 8 i hix hiy (by omega) (by omega) hslice
-- CHECKPOINT

/-- Lemma 8.1: the actual overlapping chunk representation loses no long message. -/
theorem encoding_injective_long : EncodingInjectiveLong := by
  intro x y hx hy he
  exact chunkAt_recovers_message x y hx (encode_recovers_length x y (by omega) (by omega) he)
    (chunkAt_eq_of_encode_eq x y he)
-- CHECKPOINT

end ProvenHashes.UMASH
