import ProvenHashes.UMASHENHFibre
import ProvenHashes.UMASHShortProbability

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb

def lowENHXor (n δ ε A B : ℕ) : ℕ :=
  (A*B % 2^n) ^^^ ((A+δ)*(B+ε) % 2^n)

theorem lowENHXor_lt (n δ ε A B : ℕ) : lowENHXor n δ ε A B < 2^n :=
  Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
-- CHECKPOINT

/-- A prescribed XOR difference gives an odd triangular congruence when δ is odd. -/
theorem lowENHXor_congruence (n δ ε A B e : ℕ) (he : e < 2^n)
    (h : lowENHXor n δ ε A B = e) :
    Int.ModEq ((2:ℤ)^n)
      ((δ:ℤ)*B+(ε:ℤ)*A+δ*ε+2*(A*B &&& e : ℕ)) (e:ℤ) := by
  let L := A*B%2^n
  let L' := (A+δ)*(B+ε)%2^n
  have hd : (L':ℤ)-L = (e:ℤ)-2*(L &&& e : ℕ) := by
    have hh := xor_signed_difference L L'
    change L ^^^ L' = e at h
    rw [h] at hh
    omega
  have hL : Int.ModEq ((2^n:ℕ):ℤ) (A*B:ℕ) (L:ℤ) :=
    Int.natCast_modEq_iff.mpr (Nat.mod_mod _ _).symm
  have hL' : Int.ModEq ((2^n:ℕ):ℤ) ((A+δ)*(B+ε):ℕ) (L':ℤ) :=
    Int.natCast_modEq_iff.mpr (Nat.mod_mod _ _).symm
  have hh := (hL'.sub hL).add_right (2*(L &&& e : ℕ):ℤ)
  rw [hd] at hh
  have hmask : L &&& e = A*B &&& e := and_mod_word n (A*B) e he
  rw [hmask] at hh
  push_cast at hh
  convert hh using 1 <;> ring
-- CHECKPOINT

theorem lowENHXor_odd_slice_injective (n δ ε A : ℕ) (hδ : δ%2 = 1) :
    Function.Injective (fun B : Fin (2^n) => lowENHXor n δ ε A B.val) := by
  intro x y hxy
  have hx := lowENHXor_congruence n δ ε A x.val (lowENHXor n δ ε A x.val)
    (lowENHXor_lt n δ ε A x.val) rfl
  have hy := lowENHXor_congruence n δ ε A y.val (lowENHXor n δ ε A x.val)
    (lowENHXor_lt n δ ε A x.val) hxy.symm
  apply Fin.ext
  refine triangular_lift_unique n (δ:ℤ) 1 ((ε:ℤ)*A+δ*ε)
    (by exact_mod_cast hδ) (fun B => A*B &&& lowENHXor n δ ε A x.val)
    ?_ x.val y.val x.isLt y.isLt ?_
  · intro a b j hab
    simpa only [Nat.xor_zero] using product_mask_prefix A (lowENHXor n δ ε A x.val) 0 a b j hab
  · convert hx.trans hy.symm using 1 <;> ring
-- CHECKPOINT

/-- PROOF3 Lemma 3.1(a), at every width, including the smaller width used by (d). -/
theorem lowENHXor_odd_uniform (n δ ε e : ℕ) (hδ : δ%2 = 1) (he : e < 2^n) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      lowENHXor n δ ε ab.1.val ab.2.val = e) = (1:ℚ≥0)/2^n := by
  apply probability_prod_eq
  intro A
  let f : Fin (2^n) → Fin (2^n) := fun B =>
    ⟨lowENHXor n δ ε A.val B.val, lowENHXor_lt n δ ε A.val B.val⟩
  have hi : Function.Injective f := by
    intro a b hab
    exact lowENHXor_odd_slice_injective n δ ε A.val hδ (congrArg Fin.val hab)
  have hp := probability_bijective_point f ⟨hi, Finite.surjective_of_injective hi⟩ ⟨e,he⟩
  simpa only [f, Fin.mk.injEq, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using hp
-- CHECKPOINT

/-- The same width-uniform result directly over two BitVec n operands. -/
theorem lowENHXor_odd_uniform_bitvec (n δ ε e : ℕ) (hδ : δ%2 = 1) (he : e < 2^n) :
    letI : Fintype (BitVec n) := Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv
    uniformProb (fun ab : BitVec n × BitVec n =>
      lowENHXor n δ ε ab.1.toNat ab.2.toNat = e) = (1:ℚ≥0)/2^n := by
  letI : Fintype (BitVec n) := Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv
  let equiv : (Fin (2^n) × Fin (2^n)) ≃ (BitVec n × BitVec n) :=
    Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv equiv]
  exact lowENHXor_odd_uniform n δ ε e hδ he
-- CHECKPOINT

end ProvenHashes.UMASH
