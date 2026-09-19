import ProvenHashes.UMASHBlockOddPH
import ProvenHashes.UMASHProjectionRefined

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul chunkCode

theorem clmul_low_bit (a b : Word) :
    (clmul a b).getLsbD 0 = (a.getLsbD 0 && b.getLsbD 0) := by
  apply bitCoeff_injective
  rw [← coeff_bitPolynomial, bitPolynomial_clmul, Polynomial.mul_coeff_zero,
    coeff_bitPolynomial, coeff_bitPolynomial]
  cases a.getLsbD 0 <;> cases b.getLsbD 0 <;> norm_num [bitCoeff]
-- CHECKPOINT

theorem clmul_top_bit (a b : Word) : (clmul a b).getLsbD 127 = false := by
  have hd (x : Word) : (bitPolynomial x).natDegree ≤ 63 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_bitPolynomial, BitVec.getLsbD_of_ge x n (by omega)]
    rfl
  have hp : (bitPolynomial a*bitPolynomial b).natDegree < 127 :=
    lt_of_le_of_lt (Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hd a) (hd b)))
      (by decide)
  apply bitCoeff_injective
  rw [← coeff_bitPolynomial, bitPolynomial_clmul,
    Polynomial.coeff_eq_zero_of_natDegree_lt hp]
  rfl
-- CHECKPOINT

theorem word_low_bit_value (x : Word) : x.toNat%2 = (x.getLsbD 0).toNat := by
  change x.toNat%2 = (x.toNat.testBit 0).toNat
  rw [Nat.toNat_testBit]
  simp
-- CHECKPOINT

theorem word_top_bit_value (x : Word) : x.toNat/2^63 = (x.getLsbD 63).toNat := by
  change x.toNat/2^63 = (x.toNat.testBit 63).toNat
  rw [Nat.toNat_testBit]
  symm
  apply Nat.mod_eq_of_lt
  have hx := x.isLt
  norm_num at hx ⊢
  omega
-- CHECKPOINT

theorem chunkCode_xor_nat_injective {K : Type*} (x y : K → Chunk)
    (hi : Function.Injective (fun k => chunkCode (x k)+chunkCode (y k))) :
    Function.Injective (fun k =>
      ((x k).1.toNat ^^^ (y k).1.toNat, (x k).2.toNat ^^^ (y k).2.toNat)) := by
  intro a b hab
  apply hi
  have he : xorChunk (x a) (y a) = xorChunk (x b) (y b) := by
    apply Prod.ext
    · apply BitVec.eq_of_toNat_eq
      simpa only [xorChunk, BitVec.toNat_xor] using congrArg Prod.fst hab
    · apply BitVec.eq_of_toNat_eq
      simpa only [xorChunk, BitVec.toNat_xor] using congrArg Prod.snd hab
  simpa only [chunkCode_xor] using congrArg chunkCode he
-- CHECKPOINT

theorem masked_ph_even_right_probability (x y M N : Chunk) (fixed : Word)
    (hne : x.1 ≠ y.1) (hd : (x.1 ^^^ y.1).toNat%2 = 0) :
    uniformProb (fun k : Word => project (xorChunk M (ph (fixed,k) x)) =
      project (xorChunk N (ph (fixed,k) y))) ≤ (364816:ℚ≥0)/q := by
  let u := x.1 ^^^ fixed
  let v := y.1 ^^^ fixed
  let C := M.1 ^^^ N.1 ^^^ (split (clmul u x.2)).1 ^^^ (split (clmul v y.2)).1
  have huv : u ^^^ v = x.1 ^^^ y.1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [u, v, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  have hb : (u ^^^ v).getLsbD 0 = false := by
    rw [huv]
    change (x.1 ^^^ y.1).toNat.testBit 0 = false
    simp only [Nat.testBit_zero, hd, Nat.zero_ne_one, decide_false]
  have hf (d mask : Chunk) (k : Word) :
      (xorChunk mask (ph (fixed,k) d)).1 = lowAffinePH (d.1 ^^^ fixed) d.2 mask.1 k := by
    simp only [xorChunk, ph, lowAffinePH]
    rw [BitVec.xor_comm k d.2]
  have hlo (k : Word) :
      ((xorChunk M (ph (fixed,k) x)).1.toNat ^^^
        (xorChunk N (ph (fixed,k) y)).1.toNat)%2 = (C.getLsbD 0).toNat := by
    rw [← BitVec.toNat_xor, word_low_bit_value, hf, hf,
      lowAffinePH_xor]
    rw [BitVec.getLsbD_xor]
    simp only [split, BitVec.getLsbD_setWidth,
      show decide (0 < 64) = true from rfl, Bool.true_and]
    change (((clmul (u ^^^ v) k).getLsbD 0) ^^ C.getLsbD 0).toNat = _
    rw [clmul_low_bit, hb, Bool.false_and, Bool.false_xor]
  have hhi (k : Word) :
      ((xorChunk M (ph (fixed,k) x)).2.toNat ^^^
        (xorChunk N (ph (fixed,k) y)).2.toNat)/2^63 =
          ((M.2 ^^^ N.2).getLsbD 63).toNat := by
    rw [← BitVec.toNat_xor, word_top_bit_value]
    simp only [xorChunk, ph, split, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, show decide (63 < 64) = true from rfl,
      Bool.true_and, show 63+64 = 127 from rfl, clmul_top_bit, Bool.xor_false]
  have hi : Function.Injective (fun k : Word =>
      chunkCode (xorChunk M (ph (fixed,k) x))+chunkCode (xorChunk N (ph (fixed,k) y))) := by
    intro a b hab
    apply ph_code_slice_right x y hne fixed
    simp only [chunkCode_xor] at hab
    have hh := congrArg (fun z : ChunkCode => z-(chunkCode M+chunkCode N)) hab
    convert hh using 1 <;> abel
  have hw : Fintype.card Word = q :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin q)
  simpa only [hw] using projected_collision_fixed_bits_bound
    (fun k => xorChunk M (ph (fixed,k) x)) (fun k => xorChunk N (ph (fixed,k) y))
    (C.getLsbD 0) ((M.2 ^^^ N.2).getLsbD 63)
    (chunkCode_xor_nat_injective _ _ hi) hlo hhi
-- CHECKPOINT

theorem masked_ph_even_left_probability (x y M N : Chunk) (fixed : Word)
    (hne : x.2 ≠ y.2) (hd : (x.2 ^^^ y.2).toNat%2 = 0) :
    uniformProb (fun k : Word => project (xorChunk M (ph (k,fixed) x)) =
      project (xorChunk N (ph (k,fixed) y))) ≤ (364816:ℚ≥0)/q := by
  simpa only [ph, clmul_comm] using
    masked_ph_even_right_probability (x.2,x.1) (y.2,y.1) M N fixed hne hd
-- CHECKPOINT

end ProvenHashes.UMASH
