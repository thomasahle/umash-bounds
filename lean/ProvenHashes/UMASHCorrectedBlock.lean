import ProvenHashes.UMASHBlockTag
import ProvenHashes.UMASHBlockEvenPH

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

/-- Theorem 6.4: every requested primary block case is discharged. -/
theorem corrected_primary_block_bound : CorrectedPrimaryBlockBound := by
  intro seed x y hx hy hne
  by_cases hc : sameCount x y
  · by_cases hp : 0 < phDiffCount x y
    · by_cases ho : oddPH x y
      · exact (odd_ph_bound seed x y hx hy hc ho).trans (by apply NNRat.coe_le_coe.mp; norm_num [q])
      · exact even_ph_bound seed x y hx hy hc hp ho
    · have hp0 : phDiffCount x y = 0 := by omega
      by_cases hl : lastChunk x ≠ lastChunk y
      · exact (primary_enh_only_bound seed x y hx hy hc hp0 hl).trans (by apply NNRat.coe_le_coe.mp; norm_num [q])
      · have hxpos : 0 < x.chunks.length := by
          rcases hx with ⟨h0,h256,hn⟩
          omega
        have hypos : 0 < y.chunks.length := by
          change x.chunks.length = y.chunks.length at hc
          omega
        have hpre := phDiffCount_zero_prefix x y hc hp0
        have hchunks : x.chunks = y.chunks := by
          calc
            x.chunks = x.chunks.dropLast ++ [lastChunk x] :=
              block_chunks_split x (List.ne_nil_of_length_pos hxpos)
            _ = y.chunks.dropLast ++ [lastChunk y] := by rw [hpre, not_ne_iff.mp hl]
            _ = y.chunks := (block_chunks_split y (List.ne_nil_of_length_pos hypos)).symm
        have htag : blockTag seed x ≠ blockTag seed y := hne.resolve_left (not_ne_iff.mpr hchunks)
        exact (primary_tag_only_bound seed x y hx hy hchunks htag).le.trans (by apply NNRat.coe_le_coe.mp; norm_num [q])
  · exact (corrected_different_chunk_counts_bound seed x y hx hy hc).le.trans (by apply NNRat.coe_le_coe.mp; norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
