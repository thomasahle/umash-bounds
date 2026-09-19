import ProvenHashes.UMASHPolynomialCoefficients
import ProvenHashes.UMASHEncodingRecovery
import ProvenHashes.UMASHCorrectedBlock

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem valid_block_eq_of_tuple (seed : Word) (x y : Block) (hx : x.Valid) (hy : y.Valid)
    (hc : x.chunks = y.chunks) (ht : blockTag seed x = blockTag seed y) : x = y := by
  have hw : BitVec.ofNat 64 (x.byteSize%256) = BitVec.ofNat 64 (y.byteSize%256) :=
    (BitVec.xor_right_inj seed).mp ht
  have hxmod : x.byteSize%256 < 2^64 := (Nat.mod_lt _ (by decide : 0 < 256)).trans (by norm_num)
  have hymod : y.byteSize%256 < 2^64 := (Nat.mod_lt _ (by decide : 0 < 256)).trans (by norm_num)
  have he := congrArg BitVec.toNat hw
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxmod, Nat.mod_eq_of_lt hymod] at he
  have hb : x.byteSize = y.byteSize := by
    rcases hx with ⟨hx0,hx256,_⟩
    rcases hy with ⟨hy0,hy256,_⟩
    omega
  cases x
  cases y
  cases hc
  cases hb
  rfl
-- CHECKPOINT

theorem block_zero_projection_probability (seed : Word) (b : Block) (hb : b.Valid) :
    uniformProb (fun k : OHKey => project (oh k b seed) = (0,0)) < (82:ℚ≥0)/q := by
  let empty : Block := ⟨[],0⟩
  have hlen : empty.chunks.length < b.chunks.length := by
    rcases hb with ⟨h0,h256,hn⟩
    dsimp [empty]
    omega
  have h := different_chunk_counts_ordered seed empty b hb hlen
  have hz (k : OHKey) : oh k empty seed = (0,0) := rfl
  have he : primaryEvent seed empty b = (fun k => project (oh k b seed) = (0,0)) := by
    funext k
    simp [primaryEvent, hz, project, eq_comm]
  rw [he] at h
  exact h.trans_lt (by norm_num [q])
-- CHECKPOINT

theorem different_block_counts_identity_ordered (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (hc : (encode x).length < (encode y).length) :
    uniformProb (fun k : OHKey => comparisonPolynomial k seed x = comparisonPolynomial k seed y) <
      (82:ℚ≥0)/q := by
  have hyenc : (encode y) ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨b,bs,henc⟩ := List.exists_cons_of_ne_nil hyenc
  have hb : b.Valid := encoded_blocks_valid y b (by rw [henc]; exact List.mem_cons_self)
  apply (probability_mono ?_).trans_lt (block_zero_projection_probability seed b hb)
  intro k hk
  have hxshort : ¬x.length ≤ 8 := by omega
  have hyshort : ¬y.length ≤ 8 := by omega
  have he : blockPolynomial (compress false k seed x) = blockPolynomial (compress false k seed y) := by
    simpa only [comparisonPolynomial, hxshort, hyshort, ↓reduceIte] using hk
  have hlen : (compress false k seed x).length < (compress false k seed y).length := by
    simpa only [compress, List.length_map] using hc
  have hbmap : compress false k seed y = oh k b seed :: bs.map (fun b => oh k b seed) := by
    simp only [compress, henc, List.map_cons, Bool.false_eq_true, ↓reduceIte]
  rw [hbmap] at he hlen
  exact blockPolynomial_head_zero_of_shorter _ _ _ hlen he.symm
-- CHECKPOINT

theorem corrected_different_block_counts_bound : CorrectedDifferentBlockCountsBound := by
  intro seed x y hx hy hc
  rcases lt_or_gt_of_ne hc with hlt | hlt
  · exact different_block_counts_identity_ordered seed x y hx hy hlt
  · have h := different_block_counts_identity_ordered seed y x hy hx hlt
    simpa only [eq_comm] using h
-- CHECKPOINT

theorem same_block_count_identity_bound (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (hne : x ≠ y)
    (hc : (encode x).length = (encode y).length) :
    uniformProb (fun k : OHKey => comparisonPolynomial k seed x = comparisonPolynomial k seed y) ≤
      (364816:ℚ≥0)/q := by
  have henc : encode x ≠ encode y := fun h => hne (encoding_injective_long x y hx hy h)
  have hwit : ∃ i : Fin (encode x).length,
      (encode x)[i.val] ≠ (encode y)[i.val]'(by rw [← hc]; exact i.isLt) := by
    by_contra hn
    push_neg at hn
    apply henc
    apply List.ext_getElem hc
    intro i hi hiy
    exact hn ⟨i,hi⟩
  obtain ⟨i,hib⟩ := hwit
  let bx := (encode x)[i.val]
  let byy := (encode y)[i.val]'(by rw [← hc]; exact i.isLt)
  have hvx : bx.Valid := encoded_blocks_valid x bx (List.getElem_mem i.isLt)
  have hvy : byy.Valid := encoded_blocks_valid y byy (List.getElem_mem (by rw [← hc]; exact i.isLt))
  have htuple : bx.chunks ≠ byy.chunks ∨ blockTag seed bx ≠ blockTag seed byy := by
    by_contra hn
    push_neg at hn
    exact hib (valid_block_eq_of_tuple seed bx byy hvx hvy hn.1 hn.2)
  apply (probability_mono ?_).trans (corrected_primary_block_bound seed bx byy hvx hvy htuple)
  intro k hk
  have hxshort : ¬x.length ≤ 8 := by omega
  have hyshort : ¬y.length ≤ 8 := by omega
  have he : blockPolynomial (compress false k seed x) = blockPolynomial (compress false k seed y) := by
    simpa only [comparisonPolynomial, hxshort, hyshort, ↓reduceIte] using hk
  have hlen : (compress false k seed x).length = (compress false k seed y).length := by
    simpa only [compress, List.length_map] using hc
  have hp := blockPolynomial_same_length _ _ hlen he
  have hi : i.val < ((compress false k seed x).map project).length := by
    simpa only [List.length_map, compress] using i.isLt
  have hget := List.getElem_of_eq hp hi
  simpa only [compress, List.getElem_map, Bool.false_eq_true, ↓reduceIte,
    primaryEvent, bx, byy] using hget
-- CHECKPOINT

end ProvenHashes.UMASH
