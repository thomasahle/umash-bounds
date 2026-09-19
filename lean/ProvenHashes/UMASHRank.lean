import ProvenHashes.UMASHPH
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! Fibre counting for lane-wise shifted carry-less multiplication.
The first nonzero bit of a nonzero product has index v(d)+v(k).
On any fixed-output fibre, the h discarded input positions determine the key. -/
namespace ProvenHashes.UMASH

open Polynomial

theorem bitPolynomial_trailing {w : ℕ} (x : BitVec w) (hx : x ≠ 0) :
    (bitPolynomial x).natTrailingDegree < w ∧
      x.getLsbD (bitPolynomial x).natTrailingDegree = true := by
  have hc := Polynomial.coeff_natTrailingDegree_ne_zero.mpr (bitPolynomial_ne_zero hx)
  rw [coeff_bitPolynomial] at hc
  have hbit : x.getLsbD (bitPolynomial x).natTrailingDegree = true := by
    cases hb : x.getLsbD (bitPolynomial x).natTrailingDegree
    · exact False.elim (hc (by simp [hb, bitCoeff]))
    · rfl
  refine ⟨?_, hbit⟩
  by_contra hge
  rw [BitVec.getLsbD_of_ge x _ (by omega)] at hbit
  contradiction
-- CHECKPOINT

/-- A shifted lane retains every product bit outside its top h positions. -/
theorem laneShift_split_kept_bit {a b : Wide} {h n : ℕ}
    (heq : laneShift (split a) h = laneShift (split b) h)
    (hn : n < 128) (hkeep : n % 64 + h < 64) :
    a.getLsbD n = b.getLsbD n := by
  by_cases hlo : n < 64
  · have hk : n+h < 64 := by omega
    have he := congrArg (fun z : Chunk => z.1.getLsbD (n+h)) heq
    simpa [laneShift, split, BitVec.getLsbD_shiftLeft, hk,
      show ¬n+h < h by omega, hlo] using he
  · have hk : n-64+h < 64 := by omega
    have he := congrArg (fun z : Chunk => z.2.getLsbD (n-64+h)) heq
    simpa [laneShift, split, BitVec.getLsbD_shiftLeft, hk,
      show ¬n-64+h < h by omega, show n-64 < 64 by omega,
      show n-64+64 = n by omega, show 64+(n-64) = n by omega] using he
-- CHECKPOINT

/-- Input positions whose first product bit is discarded by the lane shift. -/
def discardedBits (v h : ℕ) : Finset (Fin 64) :=
  Finset.univ.filter (fun i => 64-h ≤ (v+i.val) % 64)

theorem discardedBits_card_le (v h : ℕ) (hh : h ≤ 64) :
    (discardedBits v h).card ≤ h := by
  calc
    (discardedBits v h).card ≤ (Finset.range h).card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin 64 => (v+i.val)%64 - (64-h))
      · intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        apply Finset.mem_range.mpr
        have hm := Nat.mod_lt (v+i.val) (by decide : 0 < 64)
        dsimp only
        omega
      · intro i hi j hj he
        have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        apply Fin.ext
        have him := i.isLt
        have hjm := j.isLt
        dsimp only at he
        omega
    _ = h := Finset.card_range h
-- CHECKPOINT

/-- On each shifted-product fibre, the discarded input bits determine the key. -/
theorem shifted_product_fibre_injective (d : Word) (hd : d ≠ 0) (h : ℕ)
    {a b : Word}
    (hout : laneShift (split (clmul d a)) h = laneShift (split (clmul d b)) h)
    (hbits : ∀ i ∈ discardedBits (bitPolynomial d).natTrailingDegree h,
      a.getLsbD i.val = b.getLsbD i.val) : a = b := by
  by_contra hab
  have hab0 : a ^^^ b ≠ 0 := fun h => hab (BitVec.xor_eq_zero_iff.mp h)
  let v := (bitPolynomial d).natTrailingDegree
  let t := (bitPolynomial (a ^^^ b)).natTrailingDegree
  obtain ⟨hv, _⟩ := bitPolynomial_trailing d hd
  obtain ⟨ht, htb⟩ := bitPolynomial_trailing (a ^^^ b) hab0
  have hkeep : (v+t)%64+h < 64 := by
    by_contra hn
    have hm : (⟨t, ht⟩ : Fin 64) ∈ discardedBits v h := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by dsimp only; omega⟩
    have hb := hbits ⟨t, ht⟩ hm
    have hfalse : (a ^^^ b).getLsbD t = false := by
      simp only [BitVec.getLsbD_xor, hb, Bool.xor_self]
    rw [hfalse] at htb
    contradiction
  have hkept := laneShift_split_kept_bit hout (show v+t < 128 by dsimp [v, t]; omega) hkeep
  have hzero : (bitPolynomial (clmul d (a ^^^ b))).coeff (v+t) = 0 := by
    rw [coeff_bitPolynomial, clmul_xor_right, BitVec.getLsbD_xor, hkept, Bool.xor_self]
    rfl
  have hne : (bitPolynomial (clmul d (a ^^^ b))).coeff (v+t) ≠ 0 := by
    rw [bitPolynomial_clmul]
    change (bitPolynomial d * bitPolynomial (a ^^^ b)).coeff
      ((bitPolynomial d).natTrailingDegree + (bitPolynomial (a ^^^ b)).natTrailingDegree) ≠ 0
    rw [Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree]
    exact mul_ne_zero
      (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (bitPolynomial_ne_zero hd))
      (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (bitPolynomial_ne_zero hab0))
  exact hne hzero
-- CHECKPOINT

/-- The original rank obligation, including both endpoint shifts h=0 and h=64. -/
theorem rank_lemma64 : RankLemma64 := by
  classical
  intro d hd h hh z
  let s := discardedBits (bitPolynomial d).natTrailingDegree h
  let bits (k : Word) : s → Bool := fun i => k.getLsbD i.val.val
  calc
    (Finset.univ.filter (fun k : Word => laneShift (split (clmul d k)) h = z)).card ≤
        Fintype.card (s → Bool) := by
      rw [← Finset.card_univ]
      apply Finset.card_le_card_of_injOn bits
      · intro _ _
        exact Finset.mem_univ _
      · intro a ha b hb he
        apply shifted_product_fibre_injective d hd h
        · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
        · intro i hi
          exact congrFun he ⟨i, hi⟩
    _ = 2^s.card := by simp
    _ ≤ 2^h := by
      gcongr
      · norm_num
      · exact discardedBits_card_le _ h hh
-- CHECKPOINT

end ProvenHashes.UMASH
