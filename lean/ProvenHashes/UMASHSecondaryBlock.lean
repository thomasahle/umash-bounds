import ProvenHashes.UMASHSecondaryLengths
import ProvenHashes.UMASHSecondaryTag
import ProvenHashes.UMASHSecondaryPH
import ProvenHashes.UMASHContinuationObligations

/-! PROOF5's secondary marginal bound, with all literal block cases closed. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem secondary_block_bound : SecondaryBlockBound729632 := by
  intro seed x y hx hy hne
  by_cases hc : sameCount x y
  · by_cases hs : dataChecksum x = dataChecksum y
    · by_cases hp : 0 < phDiffCount x y
      · exact secondary_equal_checksum_ph_bound seed x y hx hy hc hs hp
      · have hp0 : phDiffCount x y = 0 := by omega
        by_cases hl : lastChunk x ≠ lastChunk y
        · exact (secondary_enh_only_bound seed x y hx hy hc hp0 hl).trans
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
          exact (secondary_tag_only_bound seed x y hx hchunks htag).trans
            (by apply NNRat.coe_le_coe.mp; norm_num [q])
    · exact (secondary_different_data_checksum_bound seed x y hx hy hc hs).trans
        (by apply NNRat.coe_le_coe.mp; norm_num [q])
  · exact secondary_different_chunk_counts_bound seed x y hx hy hc
-- CHECKPOINT

end ProvenHashes.UMASH
