import ProvenHashes.UMASHJointLengths
import ProvenHashes.UMASHDifferentChecksums
import ProvenHashes.UMASHJointTag
import ProvenHashes.UMASHPHENHZero
import ProvenHashes.UMASHContinuationObligations

/-! The exhaustive joint block case split. Exactly two analytic rows remain
as explicit premises; this is not an unconditional joint collision bound. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

theorem single_ph_equal_checksum_last_ne (x y : Block) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (hp : phDiffCount x y = 1) :
    lastChunk x ≠ lastChunk y := by
  obtain ⟨i,hi,hne,ho⟩ := phDiffCount_one_index x y hc hp
  intro he
  have hd := single_ph_checksum_difference x y hc hs i hi ho
  rw [he] at hd
  have h1 := congrArg Prod.fst hd
  have h2 := congrArg Prod.snd hd
  simp only [xorChunk, BitVec.xor_self] at h1 h2
  exact hne (Prod.ext (BitVec.xor_eq_zero_iff.mp h1) (BitVec.xor_eq_zero_iff.mp h2))
-- CHECKPOINT

theorem enh_two_word_valuation_lt64 (x y : Block) (he : enhChanges x y = 2) :
    enhValuation x y < 64 := by
  have hx := (enhChanges_two_words x y he).1
  have hw : (lastChunk x).1 ^^^ (lastChunk y).1 ≠ 0 :=
    fun h => hx (BitVec.xor_eq_zero_iff.mp h)
  have hv := (bitPolynomial_trailing ((lastChunk x).1 ^^^ (lastChunk y).1) hw).1
  rw [bitPolynomial_trailing_eq_padic _ hw] at hv
  exact (min_le_left _ _).trans_lt hv
-- CHECKPOINT

theorem joint_block_bound_of_two_rows (hB : SubcaseBBound) (hW : PHOneWordENHBound) :
    JointBlockBound1416246956032 := by
  intro seed x y hx hy hne
  by_cases hc : sameCount x y
  · by_cases hs : dataChecksum x = dataChecksum y
    · by_cases hp2 : 2 ≤ phDiffCount x y
      · exact (hB seed x y hx hy hc hs hp2).trans_eq (by norm_num [q])
      · by_cases hp1 : phDiffCount x y = 1
        · have hlast := single_ph_equal_checksum_last_ne x y hc hs hp1
          have he : enhChanges x y = 1 ∨ enhChanges x y = 2 := by
            have hnot : ¬((lastChunk x).1 = (lastChunk y).1 ∧ (lastChunk x).2 = (lastChunk y).2) :=
              fun h => hlast (Prod.ext h.1 h.2)
            unfold enhChanges
            split_ifs <;> simp_all
          rcases he with he | he
          · exact (hW seed x y hx hy hc hs hp1 he).le.trans
              (by apply NNRat.coe_le_coe.mp; norm_num [q])
          · by_cases hr : enhValuation x y = 0
            · exact (joint_phenh_zero_bound seed x y hx hy hc hs hp1 he hr).trans
                (by apply NNRat.coe_le_coe.mp; norm_num [q])
            · exact (joint_phenh_sharp seed x y hx hy hc hs hp1 he (by omega)
                (by have := enh_two_word_valuation_lt64 x y he; omega)).trans
                (by apply NNRat.coe_le_coe.mp; norm_num [q])
        · have hp0 : phDiffCount x y = 0 := by omega
          by_cases hl : lastChunk x ≠ lastChunk y
          · exact (joint_enh_only_bound seed x y hx hy hc hp0 hl).trans
              (by apply NNRat.coe_le_coe.mp; norm_num [q])
          · have hxpos : 0 < x.chunks.length := by rcases hx with ⟨_,_,h⟩; omega
            have hypos : 0 < y.chunks.length := by rcases hy with ⟨_,_,h⟩; omega
            have hpre := phDiffCount_zero_prefix x y hc hp0
            have hchunks : x.chunks = y.chunks := by
              calc
                x.chunks = x.chunks.dropLast ++ [lastChunk x] :=
                  block_chunks_split x (List.ne_nil_of_length_pos hxpos)
                _ = y.chunks.dropLast ++ [lastChunk y] := by rw [hpre, not_ne_iff.mp hl]
                _ = y.chunks := (block_chunks_split y (List.ne_nil_of_length_pos hypos)).symm
            have htag := hne.resolve_left (not_ne_iff.mpr hchunks)
            exact (joint_tag_only_bound seed x y hx hy hchunks htag).le.trans
              (by apply NNRat.coe_le_coe.mp; norm_num [q])
    · exact (joint_different_data_checksum_bound seed x y hx hy hc hs).trans
        (by apply NNRat.coe_le_coe.mp; norm_num [q])
  · exact (joint_different_chunk_counts_bound seed x y hx hy hc).trans
      (by apply NNRat.coe_le_coe.mp; norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
