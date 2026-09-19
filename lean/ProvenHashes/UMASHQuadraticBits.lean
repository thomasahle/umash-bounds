import ProvenHashes.UMASHQuadraticSets

namespace ProvenHashes.UMASH
open scoped Classical
set_option maxHeartbeats 2000000

def selectedBitTargets (n : ℕ) (S : Finset (Fin n)) (a : Fin n → Bool) : Finset ℤ :=
  (Finset.Ico 0 ((2:ℤ)^n)).filter (fun z =>
    ∀ i ∈ S, (BitVec.ofInt n z).getLsbD i.val = a i)

/-- Fixing h selected bits leaves at most 2^(n-h) possible residues. -/
theorem selectedBitTargets_card_le (n : ℕ) (S : Finset (Fin n)) (a : Fin n → Bool) :
    (selectedBitTargets n S a).card ≤ 2^(n-S.card) := by
  classical
  let f (z : ℤ) : {i : Fin n // i ∉ S} → Bool :=
    fun i => (BitVec.ofInt n z).getLsbD i.val.val
  calc
    _ ≤ (Finset.univ : Finset ({i : Fin n // i ∉ S} → Bool)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro z _; exact Finset.mem_univ _
      · intro x hx y hy he
        have hx := Finset.mem_filter.mp hx
        have hy := Finset.mem_filter.mp hy
        have hxrange := Finset.mem_Ico.mp hx.1
        have hyrange := Finset.mem_Ico.mp hy.1
        have hb : BitVec.ofInt n x = BitVec.ofInt n y := by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          by_cases hS : (⟨i,hi⟩ : Fin n) ∈ S
          · exact (hx.2 ⟨i,hi⟩ hS).trans (hy.2 ⟨i,hi⟩ hS).symm
          · exact congrFun he ⟨⟨i,hi⟩,hS⟩
        have hv := congrArg BitVec.toNat hb
        simp only [BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat,
          Int.emod_eq_of_lt hxrange.1 hxrange.2,
          Int.emod_eq_of_lt hyrange.1 hyrange.2] at hv
        omega
    _ = _ := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
-- CHECKPOINT

theorem selectedBitTargets_mem (n : ℕ) (S : Finset (Fin n)) (a : Fin n → Bool) (z : ℤ) :
    z % (2:ℤ)^n ∈ selectedBitTargets n S a ↔
      ∀ i ∈ S, (BitVec.ofInt n z).getLsbD i.val = a i := by
  have hpos : 0 < (2:ℤ)^n := by positivity
  have hv : BitVec.ofInt n (z % (2:ℤ)^n) = BitVec.ofInt n z := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat, Int.emod_emod]
  simp only [selectedBitTargets, Finset.mem_filter, Finset.mem_Ico,
    Int.emod_nonneg z hpos.ne', Int.emod_lt_of_pos z hpos, and_self, true_and, hv]
-- CHECKPOINT

/-- PROOF2 Lemma 5.1 in full: any selected positions, any assignment,
arbitrary width and integer coefficients, with b or c odd. -/
theorem quadratic_selected_bits_probability (n : ℕ) (S : Finset (Fin n))
    (a : Fin n → Bool) (b c d : ℤ) (hodd : b%2 = 1 ∨ c%2 = 1) :
    uniformProb (fun x : Fin (2^n) => ∀ i ∈ S,
      (BitVec.ofInt n (b*(x.val:ℤ)^2+c*x.val+d)).getLsbD i.val = a i) ≤
      min 1 ((4:ℚ≥0)/2^(S.card/2)) := by
  have hh : S.card ≤ n := (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
  have h := quadratic_small_set_probability n S.card hh b c d
    (selectedBitTargets n S a) hodd (selectedBitTargets_card_le n S a)
  simpa only [selectedBitTargets_mem, quadraticValue] using h
-- CHECKPOINT

/-- The selected-bit bound on the same width-uniform word type as UMASH. -/
theorem quadratic_selected_bits_probability_bitvec (n : ℕ) (S : Finset (Fin n))
    (a : Fin n → Bool) (b c d : ℤ) (hodd : b%2 = 1 ∨ c%2 = 1) :
    letI : Fintype (BitVec n) := Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv
    uniformProb (fun x : BitVec n => ∀ i ∈ S,
      (BitVec.ofInt n (b*(x.toNat:ℤ)^2+c*x.toNat+d)).getLsbD i.val = a i) ≤
      min 1 ((4:ℚ≥0)/2^(S.card/2)) := by
  letI : Fintype (BitVec n) := Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv BitVec.equivFin.symm.toEquiv]
  exact quadratic_selected_bits_probability n S a b c d hodd
-- CHECKPOINT

end ProvenHashes.UMASH
