import ProvenHashes.UMASHLowTargetSparse

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
attribute [local irreducible] uniformProb

/-- An even first operand reduces the product congruence by one bit. -/
theorem even_product_mod_half (n A B t : ℕ) (hA : A%2 = 0)
    (ht : A*B%2^(n+1) = t) :
    (A/2)*(B%2^n)%2^n = t/2 := by
  have ha : A = 2*(A/2) := by omega
  have he : 2*(((A/2)*B)%2^n) = t := by
    calc
      _ = (2*((A/2)*B))%(2*2^n) := (Nat.mul_mod_mul_left _ _ _).symm
      _ = t := by
        rw [← Nat.mul_assoc, ← ha, show 2*2^n = 2^(n+1) by rw [pow_succ]; omega]
        exact ht
  have hd := congrArg (fun x => x/2) he
  simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_mod] using hd
-- CHECKPOINT

/-- Modular products have at most (n+2)2^(n-1) preimages of any target.
The doubled form includes width zero without truncated exponents. -/
theorem modular_product_count (n t : ℕ) (S : Finset (ℕ × ℕ))
    (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, ab.1*ab.2%2^n = t) :
    2*S.card ≤ (n+2)*2^n := by
  induction n generalizing t S with
  | zero =>
    have hc : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have hA := hbox a ha
      have hB := hbox b hb
      apply Prod.ext <;> simp only [pow_zero] at hA hB <;> omega
    simpa using Nat.mul_le_mul_left 2 hc
  | succ n ih =>
    let Q := 2^n
    let E := S.filter (fun ab => ab.1%2 = 0)
    let O := S.filter (fun ab => ¬ab.1%2 = 0)
    let lower (ab : ℕ × ℕ) := (ab.1/2, ab.2%Q)
    let T := E.image lower
    have hQ : 0 < Q := by dsimp only [Q]; positivity
    have hpow : 2^(n+1) = 2*Q := by dsimp only [Q]; rw [pow_succ]; omega
    have hodd : O.card ≤ Q := by
      calc
        _ ≤ (Finset.range Q).card := by
          apply Finset.card_le_card_of_injOn (fun ab : ℕ × ℕ => ab.1/2)
          · intro ab hab
            have hb := hbox ab (Finset.mem_filter.mp hab).1
            rw [hpow] at hb
            exact Finset.mem_range.mpr (by change ab.1/2 < Q; omega)
          · intro a ha b hb hh
            have hao : a.1%2 = 1 := by have := (Finset.mem_filter.mp ha).2; omega
            have hbo : b.1%2 = 1 := by have := (Finset.mem_filter.mp hb).2; omega
            have hab : a.1 = b.1 := by dsimp only at hh; omega
            have hea := hevent a (Finset.mem_filter.mp ha).1
            have heb := hevent b (Finset.mem_filter.mp hb).1
            have hba := hbox a (Finset.mem_filter.mp ha).1
            have hbb := hbox b (Finset.mem_filter.mp hb).1
            apply Prod.ext hab
            have hcop : Nat.Coprime (2^(n+1)) a.1 :=
              ((Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hao)).pow_right (n+1)).symm
            have hm : Nat.ModEq (2^(n+1)) (a.1*a.2) (a.1*b.2) := by
              rw [hab]
              simpa only [hab] using hea.trans heb.symm
            exact (hm.cancel_left_of_coprime hcop).eq_of_lt_of_lt hba.2 hbb.2
        _ = Q := Finset.card_range _
    have heven : E.card ≤ 2*T.card := by
      calc
        _ ≤ (T ×ˢ Finset.range 2).card := by
          apply Finset.card_le_card_of_injOn (fun ab : ℕ × ℕ => (lower ab,ab.2/Q))
          · intro ab hab
            have hb := hbox ab (Finset.mem_filter.mp hab).1
            rw [hpow] at hb
            refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨ab,hab,rfl⟩, ?_⟩
            exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hQ).mpr (by omega))
          · intro a ha b hb hh
            have hl := congrArg Prod.fst hh
            have hhi := congrArg Prod.snd hh
            have hfst := congrArg Prod.fst hl
            have hsnd := congrArg Prod.snd hl
            have hae := (Finset.mem_filter.mp ha).2
            have hbe := (Finset.mem_filter.mp hb).2
            have hdA := Nat.mod_add_div a.2 Q
            have hdB := Nat.mod_add_div b.2 Q
            dsimp only [lower] at hfst hsnd hhi
            apply Prod.ext
            · omega
            · rw [hsnd,hhi] at hdA
              exact hdA.symm.trans hdB
        _ = 2*T.card := by simp [Nat.mul_comm]
    have hTbox : ∀ ab ∈ T, ab.1 < 2^n ∧ ab.2 < 2^n := by
      intro ab hab
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hab
      have hb := hbox a (Finset.mem_filter.mp ha).1
      rw [hpow] at hb
      refine ⟨?_, Nat.mod_lt _ hQ⟩
      change a.1/2 < Q
      omega
    have hTe : ∀ ab ∈ T, ab.1*ab.2%2^n = t/2 := by
      intro ab hab
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hab
      exact even_product_mod_half n a.1 a.2 t (Finset.mem_filter.mp ha).2
        (hevent a (Finset.mem_filter.mp ha).1)
    have hrec := ih (t/2) T hTbox hTe
    have hcard : E.card+O.card = S.card := Finset.filter_card_add_filter_neg_card_eq_card _
    rw [hpow]
    change 2*S.card ≤ (n+1+2)*(2*Q)
    change 2*T.card ≤ (n+2)*Q at hrec
    nlinarith
-- CHECKPOINT

/-- The modular-product point bound under exact uniform sampling. -/
theorem modular_product_probability (n t : ℕ) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) => ab.1.val*ab.2.val%2^n = t) ≤
      (n+2:ℕ)/(2*(2:ℚ≥0)^n) := by
  let C := ((n+2)*2^n)/2
  have hp := fin_pair_probability_of_nat_count (2^n) C
    (fun ab : ℕ × ℕ => ab.1*ab.2%2^n = t)
    (by
      intro S hb he
      have hc := modular_product_count n t S hb he
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      simpa only [Nat.mul_comm] using hc)
  have hC : (C:ℚ≥0) ≤ (n+2:ℕ)*(2:ℚ≥0)^n/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℚ≥0) < 2)).mpr
    exact_mod_cast Nat.div_mul_le_self ((n+2)*2^n) 2
  calc
    _ ≤ (C:ℚ≥0)/((2:ℚ≥0)^n)^2 := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hp
    _ ≤ ((n+2:ℕ)*(2:ℚ≥0)^n/2)/((2:ℚ≥0)^n)^2 :=
      div_le_div_of_nonneg_right hC (by positivity)
    _ = _ := by field_simp
-- CHECKPOINT

/-- Independent uniform words remain independent uniform residues after
dropping any fixed number of high digits from each coordinate. -/
theorem uniform_pair_mod_lifts (R Q : ℕ) (hR : 0 < R) (hQ : 0 < Q)
    (E : ZMod Q × ZMod Q → Prop) :
    uniformProb (fun ab : Fin (R*Q) × Fin (R*Q) => E (ab.1.val,ab.2.val)) =
      uniformProb (fun ab : Fin Q × Fin Q => E (ab.1.val,ab.2.val)) := by
  letI : NeZero R := ⟨hR.ne'⟩
  letI : NeZero Q := ⟨hQ.ne'⟩
  let equiv := (Equiv.prodProdProdComm (Fin R) (Fin R) (Fin Q) (Fin Q)).trans
    (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  rw [← uniformProb_equiv equiv]
  apply probability_prod_eq
  intro hi
  change uniformProb (fun lo : Fin Q × Fin Q =>
    E (((lo.1.val+Q*hi.1.val:ℕ):ZMod Q),((lo.2.val+Q*hi.2.val:ℕ):ZMod Q))) = _
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
-- CHECKPOINT

/-- The point bound is invariant under translations of the two operands. -/
theorem shifted_modular_product_probability (n a b : ℕ) (t : ZMod (2^n)) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      ((ab.1.val:ZMod (2^n))+a)*((ab.2.val:ZMod (2^n))+b) = t) ≤
      (n+2:ℕ)/(2*(2:ℚ≥0)^n) := by
  let ef : Fin (2^n) ≃ ZMod (2^n) :=
    { toFun := fun x => x.val
      invFun := fun z => ⟨z.val,z.val_lt⟩
      left_inv := fun x => Fin.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt])
      right_inv := fun z => ZMod.natCast_zmod_val z }
  let equiv : (Fin (2^n) × Fin (2^n)) ≃ (ZMod (2^n) × ZMod (2^n)) :=
    Equiv.prodCongr ef ef
  have hs : uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      ((ab.1.val:ZMod (2^n))+a)*((ab.2.val:ZMod (2^n))+b) = t) =
      uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
        (ab.1.val:ZMod (2^n))*ab.2.val = t) := by
    calc
      _ = uniformProb (fun ab : ZMod (2^n) × ZMod (2^n) =>
          (ab.1+a)*(ab.2+b) = t) := uniformProb_equiv equiv _
      _ = uniformProb (fun ab : ZMod (2^n) × ZMod (2^n) => ab.1*ab.2 = t) :=
        by
          simpa only [Equiv.prodCongr_apply, Equiv.coe_addRight] using
            uniformProb_equiv (Equiv.prodCongr (Equiv.addRight (a:ZMod (2^n)))
              (Equiv.addRight (b:ZMod (2^n))))
              (fun ab : ZMod (2^n) × ZMod (2^n) => ab.1*ab.2 = t)
      _ = _ := (uniformProb_equiv equiv _).symm
  rw [hs]
  have he (ab : Fin (2^n) × Fin (2^n)) :
      (ab.1.val:ZMod (2^n))*ab.2.val = t ↔ ab.1.val*ab.2.val%2^n = t.val := by
    rw [← Nat.cast_mul, ← (ZMod.val_injective (2^n)).eq_iff, ZMod.val_natCast]
  have hh := modular_product_probability n t.val
  convert hh using 1
  exact congrArg uniformProb (funext fun ab => propext (he ab))
-- CHECKPOINT

/-- PROOF2's required 63-bit modular-product point bound on the actual words. -/
theorem shifted_halfword_product_probability (a b : ℕ) (t : ZMod (2^63)) :
    uniformProb (fun ab : Word × Word =>
      ((ab.1.toNat:ZMod (2^63))+(a:ZMod (2^63)))*((ab.2.toNat:ZMod (2^63))+(b:ZMod (2^63))) = t) ≤
      (65:ℚ≥0)/q := by
  let ef : Fin (2*2^63) ≃ Word :=
    (finCongr (by decide : 2*2^63 = 2^64)).trans
      (show Fin (2^64) ≃ Word from BitVec.equivFin.symm.toEquiv)
  let equiv : (Fin (2*2^63) × Fin (2*2^63)) ≃ (Word × Word) := Equiv.prodCongr ef ef
  rw [← uniformProb_equiv equiv]
  change uniformProb (fun ab : Fin (2*2^63) × Fin (2*2^63) =>
    ((ab.1.val:ZMod (2^63))+(a:ZMod (2^63)))*((ab.2.val:ZMod (2^63))+(b:ZMod (2^63))) = t) ≤ _
  rw [uniform_pair_mod_lifts 2 (2^63) (by decide) (by positivity)
    (fun ab => (ab.1+(a:ZMod (2^63)))*(ab.2+(b:ZMod (2^63))) = t)]
  convert shifted_modular_product_probability 63 a b t using 1 <;> norm_num [q]
-- CHECKPOINT

end ProvenHashes.UMASH
