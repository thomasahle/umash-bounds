import ProvenHashes.UMASHJointOneRow
import ProvenHashes.UMASHValuedPHENHLow
import ProvenHashes.UMASHValuedPHENHZero
import ProvenHashes.UMASHOneWordPHENHHigh
import ProvenHashes.UMASHLowLedger91

/-! Close the last joint compressor row and assemble the unconditional
all-pairs block bound. The one-word high atom uses the argument from the
GPT-6 Pro handoff of 2026-09-19; the low rows use the existing PROOF2 ledger. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem ph_one_word_enh_bound : PHOneWordENHBound := by
  intro seed x y hx hy hc hs hp he
  obtain ⟨r,hval⟩ := chunk_valuation_one_word (lastChunk x) (lastChunk y) (enhChanges_one_word x y he)
  by_cases hr0 : r = 0
  · subst r
    exact (valued_joint_phenh_zero_bound seed x y hx hy hc hs hp hval).trans_lt
      (by apply NNRat.coe_lt_coe.mp; norm_num [q])
  · by_cases hr4 : 4 ≤ r
    · exact (joint_one_word_high_bound seed x y hx hy hc hs hp he r hval hr4).trans_lt
        (by apply NNRat.coe_lt_coe.mp; norm_num [q])
    · have hxl : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
      have hyl : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
      obtain ⟨i,hi,_hne,ho⟩ := phDiffCount_one_index x y hc hp
      exact (valued_phenh_low_ledger_bound seed x y hxl hyl hc hs i hi ho r hval (by omega)).trans_lt
        (phenh_low_ledger_lt91 r (x.chunks.length-(i+1)) (by omega) (by omega) (by omega) (by omega))
-- CHECKPOINT

/-- Both analytic premises of the exhaustive block split are now proved. -/
theorem joint_block_bound : JointBlockBound1416246956032 :=
  joint_block_bound_of_one_row ph_one_word_enh_bound
-- CHECKPOINT

end ProvenHashes.UMASH
