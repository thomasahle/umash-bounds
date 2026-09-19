import ProvenHashes.UMASHLongIdentity

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

noncomputable def modePolynomial (mode : Bool) (k : OHKey) (seed : Word) (m : Message) :
    Polynomial Field :=
  if m.length ≤ 8 then Polynomial.C ((unfinalize (shortHash k seed m mode)).toNat : Field)
  else blockPolynomial (compress mode k seed m)

def modeBlock (mode : Bool) (k : OHKey) (b : Block) (seed : Word) : Chunk :=
  if mode then ohSecondary k b seed else oh k b seed

theorem modePolynomial_primary (k : OHKey) (seed : Word) (m : Message) :
    modePolynomial false k seed m = comparisonPolynomial k seed m := rfl
-- CHECKPOINT

theorem modePolynomial_eval (mode : Bool) (k : OHKey) (seed : Word) (m : Message) (f : ℕ) :
    (modePolynomial mode k seed m).eval (f : Field) =
      ((unfinalize (hashWith k f seed m mode)).toNat : Field) := by
  by_cases hm : m.length ≤ 8
  · simp [modePolynomial,hashWith,hm]
  · have ht := polyReduce_lt f (compress mode k seed m) 0 (by norm_num [q])
    norm_num only [q,Nat.reducePow] at ht
    simp [modePolynomial,hashWith,hm,unfinalize_finalize,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt ht,eval_blockPolynomial]
-- CHECKPOINT

theorem modePolynomial_degree (L : ℕ) (mode : Bool) (k : OHKey) (seed : Word) (m : Message)
    (hm : m.length ≤ 8*L) :
    (modePolynomial mode k seed m).natDegree ≤ 2*((L+31)/32) := by
  unfold modePolynomial
  split_ifs
  · simp
  · exact (blockPolynomial_degree _).trans
      (Nat.mul_le_mul_left 2 (compress_length_le L mode k seed m hm))
-- CHECKPOINT

/-- Distinct long messages with equally many encoded blocks have one common
witness position for both polynomial identities and both compressor modes. -/
theorem mode_same_count_witness (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (hne : x ≠ y)
    (hc : (encode x).length = (encode y).length) :
    ∃ bx byy : Block, bx.Valid ∧ byy.Valid ∧
      (bx.chunks ≠ byy.chunks ∨ blockTag seed bx ≠ blockTag seed byy) ∧
      ∀ (mode : Bool) (k : OHKey), modePolynomial mode k seed x = modePolynomial mode k seed y →
        project (modeBlock mode k bx seed) = project (modeBlock mode k byy seed) := by
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
  refine ⟨bx,byy,hvx,hvy,htuple,?_⟩
  intro mode k hk
  have hxshort : ¬x.length ≤ 8 := by omega
  have hyshort : ¬y.length ≤ 8 := by omega
  have he : blockPolynomial (compress mode k seed x) = blockPolynomial (compress mode k seed y) := by
    simpa only [modePolynomial,hxshort,hyshort,↓reduceIte] using hk
  have hlen : (compress mode k seed x).length = (compress mode k seed y).length := by
    simpa only [compress,List.length_map] using hc
  have hp := blockPolynomial_same_length _ _ hlen he
  have hi : i.val < ((compress mode k seed x).map project).length := by
    simpa only [List.length_map,compress] using i.isLt
  have hget := List.getElem_of_eq hp hi
  simpa only [compress,List.getElem_map,modeBlock,bx,byy] using hget
-- CHECKPOINT

/-- Unequal polynomial lengths force the first longer block to project to
zero in each mode, at the same block position. -/
theorem mode_different_count_witness (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (hc : (encode x).length < (encode y).length) :
    ∃ b : Block, b.Valid ∧ ∀ (mode : Bool) (k : OHKey),
      modePolynomial mode k seed x = modePolynomial mode k seed y →
        project (modeBlock mode k b seed) = (0,0) := by
  have hyenc : encode y ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨b,bs,henc⟩ := List.exists_cons_of_ne_nil hyenc
  have hb : b.Valid := encoded_blocks_valid y b (by rw [henc]; exact List.mem_cons_self)
  refine ⟨b,hb,?_⟩
  intro mode k hk
  have hxshort : ¬x.length ≤ 8 := by omega
  have hyshort : ¬y.length ≤ 8 := by omega
  have he : blockPolynomial (compress mode k seed x) = blockPolynomial (compress mode k seed y) := by
    simpa only [modePolynomial,hxshort,hyshort,↓reduceIte] using hk
  have hlen : (compress mode k seed x).length < (compress mode k seed y).length := by
    simpa only [compress,List.length_map] using hc
  have hbmap : compress mode k seed y = modeBlock mode k b seed :: bs.map (fun b => modeBlock mode k b seed) := by
    simp only [compress,henc,List.map_cons,modeBlock]
  rw [hbmap] at he hlen
  exact blockPolynomial_head_zero_of_shorter _ _ _ hlen he.symm
-- CHECKPOINT

end ProvenHashes.UMASH
