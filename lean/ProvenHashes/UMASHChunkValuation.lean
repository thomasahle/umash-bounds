import ProvenHashes.UMASHPHENHTargets
import ProvenHashes.UMASHLowTargetsOriented

/-! A valuation interface that treats a zero increment as divisible by every
power of two. It avoids applying `padicValNat 2 0 = 0` as a minimum valuation. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

structure ChunkValuation (x y : Chunk) (r : ℕ) : Prop where
  lt64 : r < 64
  fst_dvd : 2^r ∣ (x.1 ^^^ y.1).toNat
  snd_dvd : 2^r ∣ (x.2 ^^^ y.2).toNat
  pivot : (x.1 ≠ y.1 ∧ r = wordValuation x.1 y.1) ∨
    (x.2 ≠ y.2 ∧ r = wordValuation x.2 y.2)

theorem word_valuation_facts (a b : Word) (hab : a ≠ b) :
    wordValuation a b < 64 ∧ 2^(wordValuation a b) ∣ (a ^^^ b).toNat := by
  have hn : 0 < (a ^^^ b).toNat := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hab (BitVec.xor_eq_zero_iff.mp (BitVec.eq_of_toNat_eq h))
  exact ⟨(dyadic_increment_padic_factor 64 (a ^^^ b).toNat ⟨hn,(a ^^^ b).isLt⟩).1,
    pow_padicValNat_dvd⟩
-- CHECKPOINT

theorem chunk_valuation_one_word (x y : Chunk)
    (he : (x.1 ≠ y.1 ∧ x.2 = y.2) ∨ (x.1 = y.1 ∧ x.2 ≠ y.2)) :
    ∃ r, ChunkValuation x y r := by
  rcases he with ⟨hn,he⟩ | ⟨he,hn⟩
  · have hf := word_valuation_facts x.1 y.1 hn
    exact ⟨wordValuation x.1 y.1, hf.1, hf.2,
      by simp only [he,BitVec.xor_self,BitVec.toNat_zero,dvd_zero], Or.inl ⟨hn,rfl⟩⟩
  · have hf := word_valuation_facts x.2 y.2 hn
    exact ⟨wordValuation x.2 y.2, hf.1,
      by simp only [he,BitVec.xor_self,BitVec.toNat_zero,dvd_zero], hf.2, Or.inr ⟨hn,rfl⟩⟩
-- CHECKPOINT

theorem chunk_valuation_transfer (x y x' y' : Chunk) (r : ℕ)
    (he : xorChunk x y = xorChunk x' y') (hv : ChunkValuation x' y' r) :
    ChunkValuation x y r := by
  have h1 : x.1 ^^^ y.1 = x'.1 ^^^ y'.1 := congrArg Prod.fst he
  have h2 : x.2 ^^^ y.2 = x'.2 ^^^ y'.2 := congrArg Prod.snd he
  refine ⟨hv.lt64, by simpa only [h1] using hv.fst_dvd, by simpa only [h2] using hv.snd_dvd, ?_⟩
  rcases hv.pivot with ⟨hn,hr⟩ | ⟨hn,hr⟩
  · refine Or.inl ⟨?_,by simpa only [wordValuation,h1] using hr⟩
    intro hh
    rw [hh,BitVec.xor_self] at h1
    exact hn (BitVec.xor_eq_zero_iff.mp h1.symm)
  · refine Or.inr ⟨?_,by simpa only [wordValuation,h2] using hr⟩
    intro hh
    rw [hh,BitVec.xor_self] at h2
    exact hn (BitVec.xor_eq_zero_iff.mp h2.symm)
-- CHECKPOINT

theorem ph_low_xor_oriented_probability (x y : Chunk) (z : Word)
    (hx : x.1 ≠ y.1) (r : ℕ) (hr : r = wordValuation x.1 y.1) :
    uniformProb (fun k : Chunk => (ph k x).1 ^^^ (ph k y).1 = z) ≤
      ((2^r : ℕ):ℚ≥0)/q := by
  apply probability_prod_le
  intro fixed
  have hcancel : (x.1 ^^^ fixed) ^^^ (y.1 ^^^ fixed) = x.1 ^^^ y.1 := by
    rw [BitVec.xor_comm y.1 fixed,BitVec.xor_assoc,
      ← BitVec.xor_assoc fixed fixed y.1,BitVec.xor_self,BitVec.zero_xor]
  have hd : (x.1 ^^^ fixed) ^^^ (y.1 ^^^ fixed) ≠ 0 := by
    rw [hcancel]
    exact fun h => hx (BitVec.xor_eq_zero_iff.mp h)
  have hf (d : Chunk) (k : Word) :
      (ph (fixed,k) d).1 = lowAffinePH (d.1 ^^^ fixed) d.2 0 k := by
    simp only [ph,lowAffinePH]
    rw [BitVec.xor_comm k d.2]
    exact BitVec.zero_xor.symm
  simp only [hf]
  exact low_affine_xor_target_probability _ _ _ _ _ _ z hd r
    (by simpa only [hcancel,wordValuation] using hr)
-- CHECKPOINT

theorem ph_low_target_chunk_valuation (x y : Chunk) (z : Word) (r : ℕ)
    (hv : ChunkValuation x y r) :
    uniformProb (fun k : Chunk => (ph k x).1 ^^^ (ph k y).1 = z) ≤
      ((2^r : ℕ):ℚ≥0)/q := by
  rcases hv.pivot with ⟨hn,hr⟩ | ⟨hn,hr⟩
  · exact ph_low_xor_oriented_probability x y z hn r hr
  · rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => (ph k x).1 ^^^ (ph k y).1 = z)]
    simpa only [ph,clmul_comm] using ph_low_xor_oriented_probability (x.2,x.1) (y.2,y.1) z hn r hr
-- CHECKPOINT

theorem chunk_valuation_increments (x y : Chunk) (r : ℕ) (hv : ChunkValuation x y r) :
    2^r ∣ (y.1-x.1).toNat ∧ 2^r ∣ (y.2-x.2).toNat ∧
    (((y.1-x.1).toNat/2^r)%2 = 1 ∨ ((y.2-x.2).toNat/2^r)%2 = 1) := by
  have factor (a b : Word) (hn : a ≠ b) (hr : r = wordValuation a b) :
      ((b-a).toNat/2^r)%2 = 1 := by
    have hp : 0 < (b-a).toNat := by
      apply Nat.pos_of_ne_zero
      intro h
      exact hn (sub_eq_zero.mp (BitVec.eq_of_toNat_eq h)).symm
    rw [hr,wordValuation_eq_sub a b hn]
    exact (dyadic_increment_padic_factor 64 (b-a).toNat ⟨hp,(b-a).isLt⟩).2.2
  refine ⟨(word_prefix_eq_iff_sub_dvd _ _ r hv.lt64.le).mp
    ((word_prefix_eq_iff_xor_dvd _ _ r).mpr hv.fst_dvd),
    (word_prefix_eq_iff_sub_dvd _ _ r hv.lt64.le).mp
    ((word_prefix_eq_iff_xor_dvd _ _ r).mpr hv.snd_dvd), ?_⟩
  rcases hv.pivot with ⟨hn,hr⟩ | ⟨hn,hr⟩
  · exact Or.inl (factor _ _ hn hr)
  · exact Or.inr (factor _ _ hn hr)
-- CHECKPOINT

theorem enh_low_target_chunk_valuation (x y : Chunk) (tag tag' e : Word) (r : ℕ)
    (hv : ChunkValuation x y r) (hr1 : 1 ≤ r) (hd : 2^r ∣ e.toNat) :
    uniformProb (fun k : Chunk => (enh k x tag).1 ^^^ (enh k y tag').1 = e) ≤
      lowTargetK r e.toNat/q := by
  let trans : Chunk ≃ Chunk := Equiv.prodCongr (Equiv.addLeft x.1) (Equiv.addLeft x.2)
  let E (ab : Chunk) : Prop := lowENHXor 64 (y.1-x.1).toNat (y.2-x.2).toNat
    ab.1.toNat ab.2.toNat = e.toNat
  have hred : uniformProb (fun k : Chunk => (enh k x tag).1 ^^^ (enh k y tag').1 = e) ≤ uniformProb E := by
    rw [← uniformProb_equiv trans E]
    apply probability_mono
    intro k hk
    have hh := congrArg BitVec.toNat hk
    rw [enh_low_xor_to_operands] at hh
    exact hh
  apply hred.trans
  obtain ⟨hd1,hd2,ho⟩ := chunk_valuation_increments x y r hv
  rcases ho with ho | ho
  · exact low_target_probability_oriented _ _ r e.toNat hv.lt64 hr1 hd1 hd2 ho e.isLt hd
  · change uniformProb (fun ab : Chunk => lowENHXor 64 _ _ ab.1.toNat ab.2.toNat = _) ≤ _
    rw [low_xor_probability_swap]
    exact low_target_probability_oriented _ _ r e.toNat hv.lt64 hr1 hd2 hd1 ho e.isLt hd
-- CHECKPOINT

end ProvenHashes.UMASH
