import ProvenHashes.UMASHModePolynomial
import ProvenHashes.UMASHLastUpdateCancellation

/-! Message classification for the primary argument from the GPT-6 Pro handoff of 2026-09-19,
Section 7. Full blocks precede the last block; equality of literal prefixes
cancels the actual accumulator before the final update. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem encoded_earlier_full (m : Message) (i : ℕ) (hi : i+1 < (encode m).length) :
    ((encode m)[i]'(by omega)).byteSize = 256 := by
  have hn := hi
  rw [encode_length] at hn
  have hs : 256 ≤ m.length-256*i := by omega
  simp only [encode,List.getElem_map,List.getElem_range,encodeBlock]
  exact Nat.min_eq_left hs
-- CHECKPOINT

theorem mode_identity_at_index (mode : Bool) (k : OHKey) (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (hc : (encode x).length = (encode y).length)
    (i : ℕ) (hi : i < (encode x).length)
    (he : modePolynomial mode k seed x = modePolynomial mode k seed y) :
    project (modeBlock mode k ((encode x)[i]) seed) =
      project (modeBlock mode k ((encode y)[i]'(by omega)) seed) := by
  have hp : blockPolynomial (compress mode k seed x) = blockPolynomial (compress mode k seed y) := by
    simpa only [modePolynomial,if_neg (by omega : ¬x.length ≤ 8),
      if_neg (by omega : ¬y.length ≤ 8)] using he
  have hlen : (compress mode k seed x).length = (compress mode k seed y).length := by
    simpa only [compress,List.length_map] using hc
  have hlist := blockPolynomial_same_length _ _ hlen hp
  have hij : i < ((compress mode k seed x).map project).length := by
    simpa only [compress,List.length_map] using hi
  have hget := List.getElem_of_eq hlist hij
  simpa only [compress,List.getElem_map,modeBlock] using hget
-- CHECKPOINT

theorem long_primary_message_cases (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (hne : x ≠ y)
    (hc : (encode x).length = (encode y).length) :
    (∃ bx byy : Block, bx.Valid ∧ byy.Valid ∧ bx.byteSize = 256 ∧ byy.byteSize = 256 ∧
      bx.chunks ≠ byy.chunks ∧ ∀ k : OHKey,
        comparisonPolynomial k seed x = comparisonPolynomial k seed y → primaryEvent seed bx byy k) ∨
    (∃ (bs : List Block) (bx byy : Block), bx.Valid ∧ byy.Valid ∧
      (bx.chunks ≠ byy.chunks ∨ blockTag seed bx ≠ blockTag seed byy) ∧
      encode x = bs++[bx] ∧ encode y = bs++[byy]) := by
  classical
  by_cases hearly : ∃ i : ℕ, ∃ hi : i+1 < (encode x).length,
      (encode x)[i]'(by omega) ≠ (encode y)[i]'(by omega)
  · obtain ⟨i,hi,hneblock⟩ := hearly
    let bx := (encode x)[i]'(by omega)
    let byy := (encode y)[i]'(by omega)
    have hfullx : bx.byteSize = 256 := encoded_earlier_full x i hi
    have hfully : byy.byteSize = 256 := encoded_earlier_full y i (by omega)
    have hchunks : bx.chunks ≠ byy.chunks := by
      intro he
      have hs : bx.byteSize = byy.byteSize := hfullx.trans hfully.symm
      apply hneblock
      exact congrArg₂ Block.mk he hs
    refine Or.inl ⟨bx,byy,encoded_blocks_valid x bx (List.getElem_mem (by omega)),
      encoded_blocks_valid y byy (List.getElem_mem (by omega)),hfullx,hfully,hchunks,?_⟩
    intro k hk
    exact mode_identity_at_index false k seed x y hx hy hc i (by omega) hk
  · have hxenc : encode x ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [encode_length]
      omega
    have hyenc : encode y ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [← hc]
      exact List.length_pos_iff.mpr hxenc
    have hprefix : (encode x).dropLast = (encode y).dropLast := by
      apply List.ext_getElem (by simp only [List.length_dropLast,hc])
      intro i hi hiy
      have hir : i+1 < (encode x).length := by rw [List.length_dropLast] at hi; omega
      have he : (encode x)[i]'(by omega) = (encode y)[i]'(by omega) := by
        by_contra hn
        exact hearly ⟨i,hir,hn⟩
      simpa only [List.getElem_dropLast] using he
    let bx := (encode x).getLast hxenc
    let byy := (encode y).getLast hyenc
    have hvx : bx.Valid := encoded_blocks_valid x bx (List.getLast_mem hxenc)
    have hvy : byy.Valid := encoded_blocks_valid y byy (List.getLast_mem hyenc)
    have hlast : bx ≠ byy := by
      intro he
      apply hne
      apply encoding_injective_long x y hx hy
      rw [← List.dropLast_append_getLast hxenc,← List.dropLast_append_getLast hyenc,hprefix]
      exact congrArg (fun b => (encode y).dropLast++[b]) he
    have ht : bx.chunks ≠ byy.chunks ∨ blockTag seed bx ≠ blockTag seed byy := by
      by_contra hn
      push_neg at hn
      exact hlast (valid_block_eq_of_tuple seed bx byy hvx hvy hn.1 hn.2)
    refine Or.inr ⟨(encode x).dropLast,bx,byy,hvx,hvy,ht,
      (List.dropLast_append_getLast hxenc).symm,?_⟩
    rw [hprefix]
    exact (List.dropLast_append_getLast hyenc).symm
-- CHECKPOINT

theorem hashWith_common_prefix_last_iff (k : OHKey) (f : ℕ) (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (bs : List Block) (bx byy : Block)
    (hex : encode x = bs++[bx]) (hey : encode y = bs++[byy]) :
    hashWith k f seed x = hashWith k f seed y ↔
      polyStep f 0 (oh k bx seed) = polyStep f 0 (oh k byy seed) := by
  simp only [hashWith,if_neg (by omega : ¬x.length ≤ 8),
    if_neg (by omega : ¬y.length ≤ 8),compress,hex,hey,List.map_append,
    List.map_cons,List.map_nil,Bool.false_eq_true,↓reduceIte]
  exact finalized_polyReduce_last_cancel f 0 _ _ _
-- CHECKPOINT

end ProvenHashes.UMASH
