import ProvenHashes.UMASHLowTargetQuadratic
import ProvenHashes.UMASHQuadraticOdd

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb

/-- Zero XOR is precisely zero additive difference, at every word width. -/
theorem lowENHXor_zero_iff_width (n δ ε A B : ℕ) :
    lowENHXor n δ ε A B = 0 ↔
      (δ:ZMod (2^n))*B+(ε:ZMod (2^n))*A+(δ:ZMod (2^n))*ε = 0 := by
  rw [lowENHXor, Nat.xor_eq_zero]
  change Nat.ModEq (2^n) (A*B) ((A+δ)*(B+ε)) ↔ _
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  constructor <;> intro h <;> linear_combination -h
-- CHECKPOINT

/-- The additive-difference distribution at any width. The second increment
may be zero; the first divided increment is odd. -/
theorem low_additive_distribution_width (n r δ ε : ℕ) (hr : r ≤ n)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (hodd : (δ/2^r)%2 = 1)
    (t : ℕ) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      (δ:ZMod (2^n))*ab.2.val+(ε:ZMod (2^n))*ab.1.val+
        (δ:ZMod (2^n))*ε = ((2^r*t:ℕ):ZMod (2^n))) =
      (2:ℚ≥0)^r/(2:ℚ≥0)^n := by
  let R := 2^r
  let Q := 2^(n-r)
  have hR : 0 < R := by dsimp [R]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hN : 2^n = R*Q := by
    dsimp [R, Q]
    rw [← pow_add, Nat.add_sub_of_le hr]
  have hd : R*(δ/R) = δ := Nat.mul_div_cancel' hδ
  have he : R*(ε/R) = ε := Nat.mul_div_cancel' hε
  have ha : Nat.Coprime (δ/R) Q :=
    (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd)).pow_right (n-r)
  apply probability_prod_eq
  intro A
  have ht (u v : ℕ) :
      (δ:ZMod (2^n))*v+(ε:ZMod (2^n))*u+(δ:ZMod (2^n))*ε =
          ((R*t:ℕ):ZMod (2^n)) ↔
      ((δ/R:ℕ):ZMod Q)*(v:ZMod Q)+
          ((ε/R*u+δ*(ε/R):ℕ):ZMod Q) = (t:ZMod Q) := by
    have hn : δ*v+ε*u+δ*ε =
        R*((δ/R)*v+(ε/R*u+δ*(ε/R))) := by
      calc
        _ = (R*(δ/R))*v+(R*(ε/R))*u+δ*(R*(ε/R)) := by rw [hd, he]
        _ = _ := by ring
    simp only [← Nat.cast_mul, ← Nat.cast_add]
    rw [hn, hN, scaled_natCast_eq_iff R Q _ _ (by omega)]
  trans uniformProb (fun B : Fin (2^n) =>
    ((δ/R:ℕ):ZMod Q)*(B.val:ZMod Q)+
      ((ε/R*A.val+δ*(ε/R):ℕ):ZMod Q) = (t:ZMod Q))
  · exact congrArg uniformProb (funext (fun B => propext (ht A.val B.val)))
  let e : Fin (2^n) ≃ Fin (R*Q) := finCongr hN
  change uniformProb (fun B : Fin (2^n) =>
    ((δ/R:ℕ):ZMod Q)*((e B).val:ZMod Q)+
      ((ε/R*A.val+δ*(ε/R):ℕ):ZMod Q) = (t:ZMod Q)) = _
  rw [uniformProb_equiv e (fun B =>
    ((δ/R:ℕ):ZMod Q)*(B.val:ZMod Q)+
      ((ε/R*A.val+δ*(ε/R):ℕ):ZMod Q) = (t:ZMod Q)),
    fin_affine_probability R Q (δ/R) hR hQ ha]
  have hNr : (2:ℚ≥0)^n = (R:ℚ≥0)*(Q:ℚ≥0) := by exact_mod_cast hN
  have hRc : (R:ℚ≥0) = (2:ℚ≥0)^r := by simp only [R, Nat.cast_pow, Nat.cast_ofNat]
  rw [hNr, ← hRc]
  have hRn : (R:ℚ≥0) ≠ 0 := by exact_mod_cast hR.ne'
  field_simp
-- CHECKPOINT

/-- PROOF3 Lemma 3.1(b), in an oriented form covering a zero second increment. -/
theorem lowENHXor_zero_uniform (n r δ ε : ℕ) (hr : r ≤ n)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (hodd : (δ/2^r)%2 = 1) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      lowENHXor n δ ε ab.1.val ab.2.val = 0) =
      (2:ℚ≥0)^r/(2:ℚ≥0)^n := by
  have h := low_additive_distribution_width n r δ ε hr hδ hε hodd 0
  simp only [Nat.mul_zero, Nat.cast_zero] at h
  rw [← h]
  exact congrArg uniformProb (funext fun ab =>
    propext (lowENHXor_zero_iff_width n δ ε ab.1.val ab.2.val))
-- CHECKPOINT

theorem lowENHXor_zero_uniform_bitvec (n r δ ε : ℕ) (hr : r ≤ n)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (hodd : (δ/2^r)%2 = 1) :
    letI : Fintype (BitVec n) := Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv
    uniformProb (fun ab : BitVec n × BitVec n =>
      lowENHXor n δ ε ab.1.toNat ab.2.toNat = 0) =
      (2:ℚ≥0)^r/(2:ℚ≥0)^n := by
  letI : Fintype (BitVec n) := Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv
  let equiv : (Fin (2^n) × Fin (2^n)) ≃ (BitVec n × BitVec n) :=
    Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv equiv]
  exact lowENHXor_zero_uniform n r δ ε hr hδ hε hodd
-- CHECKPOINT

end ProvenHashes.UMASH
