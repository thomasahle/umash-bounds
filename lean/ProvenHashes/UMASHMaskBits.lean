import ProvenHashes.UMASHQuadraticBits

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

def maskBitSet (n e : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => e.testBit i.val = true)

def maskValueTargets (n e z : ℕ) : Finset ℕ :=
  (Finset.range (2^n)).filter (fun u => u &&& e = z)

def submaskTargets (n e : ℕ) : Finset ℕ :=
  (Finset.range (2^n)).filter (fun z => z &&& e = z)

def taggedMaskTargets (n tag e z : ℕ) : Finset ℕ :=
  (Finset.range (2^n)).filter (fun H => ((H+tag)%2^n) &&& e = z)

/-- Fixing the bits selected by a mask leaves at most 2^(n-h) words. -/
theorem mask_value_targets_card_le (n e z : ℕ) :
    (maskValueTargets n e z).card ≤ 2^(n-(maskBitSet n e).card) := by
  classical
  calc
    _ ≤ (selectedBitTargets n (maskBitSet n e) (fun i => z.testBit i.val)).card := by
      apply Finset.card_le_card_of_injOn (fun u : ℕ => (u:ℤ))
      · intro u hu
        have hu := Finset.mem_filter.mp hu
        have hur : u < 2^n := Finset.mem_range.mp hu.1
        have hurZ : (u:ℤ) < (2:ℤ)^n := by exact_mod_cast hur
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Ico.mpr ⟨by positivity, hurZ⟩, ?_⟩
        intro i hi
        have hbit : e.testBit i.val = true := (Finset.mem_filter.mp hi).2
        have he := congrArg (fun v : ℕ => v.testBit i.val) hu.2
        simp only [Nat.testBit_and, hbit, Bool.and_true] at he
        have hv : (BitVec.ofInt n (u:ℤ)).toNat = u := by
          simp only [BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat,
            Int.emod_eq_of_lt (by positivity) hurZ, Int.toNat_natCast]
        change (BitVec.ofInt n (u:ℤ)).toNat.testBit i.val = z.testBit i.val
        rw [hv]
        exact he
      · intro x _ y _ he
        change (x:ℤ) = (y:ℤ) at he
        exact_mod_cast he
    _ ≤ _ := selectedBitTargets_card_le n (maskBitSet n e) (fun i => z.testBit i.val)
-- CHECKPOINT

/-- A submask is reconstructed from its bits at the selected positions. -/
theorem submask_targets_card_le (n e : ℕ) :
    (submaskTargets n e).card ≤ 2^(maskBitSet n e).card := by
  classical
  let S := maskBitSet n e
  let f (z : ℕ) : {i : Fin n // i ∈ S} → Bool := fun i => z.testBit i.val.val
  calc
    _ ≤ (Finset.univ : Finset ({i : Fin n // i ∈ S} → Bool)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro z _; exact Finset.mem_univ _
      · intro x hx y hy he
        have hx := Finset.mem_filter.mp hx
        have hy := Finset.mem_filter.mp hy
        apply Nat.eq_of_testBit_eq
        intro i
        by_cases hi : i < n
        · cases hb : e.testBit i with
          | false =>
            have hxb := congrArg (fun z : ℕ => z.testBit i) hx.2
            have hyb := congrArg (fun z : ℕ => z.testBit i) hy.2
            simp only [Nat.testBit_and, hb, Bool.and_false] at hxb hyb
            exact hxb.symm.trans hyb
          | true =>
            have hmem : (⟨i,hi⟩ : Fin n) ∈ S := by
              simp only [S, maskBitSet, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hb
            exact congrFun he ⟨⟨i,hi⟩,hmem⟩
        · have hp : 2^n ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
          rw [Nat.testBit_lt_two_pow ((Finset.mem_range.mp hx.1).trans_le hp),
            Nat.testBit_lt_two_pow ((Finset.mem_range.mp hy.1).trans_le hp)]
    _ = _ := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
-- CHECKPOINT

/-- Tag addition modulo the word size preserves the target cardinality bound. -/
theorem tagged_mask_targets_card_le (n tag e z : ℕ) :
    (taggedMaskTargets n tag e z).card ≤ 2^(n-(maskBitSet n e).card) := by
  classical
  calc
    _ ≤ (maskValueTargets n e z).card := by
      apply Finset.card_le_card_of_injOn (fun H : ℕ => (H+tag)%2^n)
      · intro H hH
        have hH := Finset.mem_filter.mp hH
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by positivity)), hH.2⟩
      · intro x hx y hy he
        have hx := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
        have hy := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
        have hm : Nat.ModEq (2^n) (x+tag) (y+tag) := he
        have hc := hm.add_right_cancel' tag
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hc
    _ ≤ _ := mask_value_targets_card_le n e z
-- CHECKPOINT

theorem mask_bit_set_card_le (n e : ℕ) : (maskBitSet n e).card ≤ n := by
  calc
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by simp
-- CHECKPOINT

end ProvenHashes.UMASH
