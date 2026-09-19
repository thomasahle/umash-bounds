import ProvenHashes.UMASHWrappedLineCount
import ProvenHashes.UMASHMaskBits
import ProvenHashes.UMASHENHFibre

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- Equation (12) in PROOF2: common low words and a prescribed high XOR
pattern determine a full product-difference residue modulo Q squared. -/
theorem high_xor_product_residue (Q A B A' B' tag tag' e : ℕ)
    (hlo : A*B%Q = A'*B'%Q)
    (hxor : ((A*B/Q+tag)%Q) ^^^ ((A'*B'/Q+tag')%Q) = e) :
    Int.ModEq ((Q:ℤ)^2) ((A':ℤ)*B'-(A:ℤ)*B)
      ((Q:ℤ)*((e:ℤ)-2*(((A*B/Q+tag)%Q &&& e:ℕ):ℤ)-((tag':ℤ)-tag))) := by
  let U := (A*B/Q+tag)%Q
  let V := (A'*B'/Q+tag')%Q
  have huv : (V:ℤ)-U = (e:ℤ)-2*(U &&& e:ℕ) := by
    have hd := xor_signed_difference U V
    change U ^^^ V = e at hxor
    rw [hxor] at hd
    omega
  have hU : Int.ModEq (Q:ℤ) ((A*B/Q+tag:ℕ):ℤ) (U:ℤ) :=
    Int.natCast_modEq_iff.mpr (Nat.mod_mod _ _).symm
  have hV : Int.ModEq (Q:ℤ) ((A'*B'/Q+tag':ℕ):ℤ) (V:ℤ) :=
    Int.natCast_modEq_iff.mpr (Nat.mod_mod _ _).symm
  have hh := (hV.sub hU).add_right (-((tag':ℤ)-tag))
  rw [huv] at hh
  have hhigh : Int.ModEq (Q:ℤ) ((A'*B'/Q:ℕ)-(A*B/Q:ℕ):ℤ)
      ((e:ℤ)-2*(U &&& e:ℕ)-((tag':ℤ)-tag)) := by
    convert hh using 1 <;> push_cast <;> ring
  have hprod : (A':ℤ)*B'-(A:ℤ)*B =
      (Q:ℤ)*((A'*B'/Q:ℕ)-(A*B/Q:ℕ):ℤ) := by
    have h₁ : (A:ℤ)*B = (A*B%Q:ℕ)+(Q:ℤ)*(A*B/Q:ℕ) := by
      exact_mod_cast (Nat.mod_add_div (A*B) Q).symm
    have h₂ : (A':ℤ)*B' = (A'*B'%Q:ℕ)+(Q:ℤ)*(A'*B'/Q:ℕ) := by
      exact_mod_cast (Nat.mod_add_div (A'*B') Q).symm
    rw [h₁, h₂, hlo]
    ring
  have hm := hhigh.mul_left' (c := (Q:ℤ))
  simpa only [← pow_two, ← hprod, U] using hm
-- CHECKPOINT

def highXorEventNat (n δ ε tag tag' e : ℕ) (ab : ℕ × ℕ) : Prop :=
  ab.1*ab.2%2^n = ((ab.1+δ)%2^n)*((ab.2+ε)%2^n)%2^n ∧
    ((ab.1*ab.2/2^n+tag)%2^n) ^^^
      (((((ab.1+δ)%2^n)*((ab.2+ε)%2^n))/2^n+tag')%2^n) = e

def highXorPattern (n tag e : ℕ) (ab : ℕ × ℕ) : ℕ :=
  ((ab.1*ab.2/2^n+tag)%2^n) &&& e

/-- The quadratic count for one high-XOR pattern, after the exact cast
from bounded natural operands to the integer-line model. -/
theorem high_xor_pattern_count (n δ ε tag tag' e z : ℕ) (S : Finset (ℕ × ℕ))
    (hδ : 0 < δ ∧ δ < 2^n) (hε : 0 < ε ∧ ε < 2^n)
    (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, highXorEventNat n δ ε tag tag' e ab)
    (hpat : ∀ ab ∈ S, highXorPattern n tag e ab = z) :
    (S.card:ℝ) ≤ 16*(Real.sqrt (((taggedMaskTargets n tag e z).card:ℝ)*(2:ℝ)^n)+
      (taggedMaskTargets n tag e z).card) := by
  classical
  let f : ℕ × ℕ → ℤ × ℤ := fun ab => ((ab.1:ℤ), (ab.2:ℤ))
  let H : Finset ℤ := (taggedMaskTargets n tag e z).image (fun h : ℕ => (h:ℤ))
  have hf : Function.Injective f := by
    intro a b he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    apply Prod.ext
    · change (a.1:ℤ) = (b.1:ℤ) at h₁
      exact_mod_cast h₁
    · change (a.2:ℤ) = (b.2:ℤ) at h₂
      exact_mod_cast h₂
  have hcardS : (S.image f).card = S.card := Finset.card_image_of_injective _ hf
  have hcardH : H.card = (taggedMaskTargets n tag e z).card :=
    Finset.card_image_of_injective _ (by
      intro x y he
      change (x:ℤ) = (y:ℤ) at he
      exact_mod_cast he)
  have hQ : (0:ℤ) < (2^n:ℕ) := by positivity
  have hδZ : (0:ℤ) < δ ∧ (δ:ℤ) < (2^n:ℕ) := by exact_mod_cast hδ
  have hεZ : (0:ℤ) < ε ∧ (ε:ℤ) < (2^n:ℕ) := by exact_mod_cast hε
  have hc := wrapped_product_high_set_count (2^n:ℕ) δ ε
    (((2^n:ℕ):ℤ)*((e:ℤ)-2*z-((tag':ℤ)-tag))) H (S.image f) hQ hδZ hεZ
    (by
      intro w hw
      obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hw
      have hb := hbox ab hab
      dsimp only [f]
      exact ⟨⟨by positivity, by exact_mod_cast hb.1⟩,
        ⟨by positivity, by exact_mod_cast hb.2⟩⟩)
    (by
      intro w hw
      obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hw
      have he := hevent ab hab
      have hp := high_xor_product_residue (2^n) ab.1 ab.2
        ((ab.1+δ)%2^n) ((ab.2+ε)%2^n) tag tag' e he.1 he.2
      have hpp := hpat ab hab
      unfold highXorPattern at hpp
      rw [hpp] at hp
      convert hp using 1 <;> dsimp only [wrappedProductDifferenceZ, f] <;> push_cast <;> rfl)
    (by
      intro w hw
      obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hw
      apply Finset.mem_image.mpr
      refine ⟨ab.1*ab.2/2^n, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr ?_, hpat ab hab⟩
        apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^n)).mpr
        have hb := hbox ab hab
        calc
          ab.1*ab.2 ≤ ab.1*2^n := Nat.mul_le_mul_left _ hb.2.le
          _ < 2^n*2^n := Nat.mul_lt_mul_of_pos_right hb.1 (by positivity)
      · dsimp only [f]
        push_cast
        rfl)
  simpa only [hcardS, hcardH, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
    Nat.cast_pow, Nat.cast_ofNat] using hc
-- CHECKPOINT

/-- The certificate uses an integer power above the real square root. -/
theorem dyadic_high_pattern_bound (n h M : ℕ) (hh : h ≤ n) (hM : M ≤ 2^(n-h)) :
    16*(Real.sqrt ((M:ℝ)*(2:ℝ)^n)+M) ≤
      16*((2:ℝ)^(n-h/2)+(2:ℝ)^(n-h)) := by
  have hs : M*2^n ≤ (2^(n-h/2))^2 := by
    calc
      M*2^n ≤ 2^(n-h)*2^n := Nat.mul_le_mul_right _ hM
      _ = 2^(n-h+n) := (pow_add _ _ _).symm
      _ ≤ 2^((n-h/2)*2) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (2^(n-h/2))^2 := pow_mul _ _ _
  have hsR : (M:ℝ)*(2:ℝ)^n ≤ ((2:ℝ)^(n-h/2))^2 := by exact_mod_cast hs
  have hroot : Real.sqrt ((M:ℝ)*(2:ℝ)^n) ≤ (2:ℝ)^(n-h/2) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hsR⟩
  have hMR : (M:ℝ) ≤ (2:ℝ)^(n-h) := by exact_mod_cast hM
  linarith
-- CHECKPOINT

/-- Summing the 2^h patterns gives the integer-ceiling form in PROOF2. -/
theorem dyadic_high_pattern_sum (n h : ℕ) (hh : h ≤ n) :
    (2:ℝ)^h*(16*((2:ℝ)^(n-h/2)+(2:ℝ)^(n-h))) =
      16*((2:ℝ)^((h+1)/2)+1)*(2:ℝ)^n := by
  have h₁ : h+(n-h/2) = n+(h+1)/2 := by omega
  have h₂ : h+(n-h) = n := by omega
  calc
    _ = 16*((2:ℝ)^h*(2:ℝ)^(n-h/2)+(2:ℝ)^h*(2:ℝ)^(n-h)) := by ring
    _ = 16*((2:ℝ)^(n+(h+1)/2)+(2:ℝ)^n) := by
      rw [← pow_add, ← pow_add, h₁, h₂]
    _ = _ := by rw [pow_add]; ring
-- CHECKPOINT

/-- PROOF2 Lemma 4.2 as an exact integer count, using ceil(h/2). It is
uniform in the width and in both tags, and requires only nonzero increments. -/
theorem high_xor_quadratic_count (n δ ε tag tag' e : ℕ) (S : Finset (ℕ × ℕ))
    (hδ : 0 < δ ∧ δ < 2^n) (hε : 0 < ε ∧ ε < 2^n)
    (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, highXorEventNat n δ ε tag tag' e ab) :
    S.card ≤ 16*(2^(((maskBitSet n e).card+1)/2)+1)*2^n := by
  classical
  let h := (maskBitSet n e).card
  let G : ℕ → Finset (ℕ × ℕ) := fun z => S.filter (fun ab => highXorPattern n tag e ab = z)
  let C : ℝ := 16*((2:ℝ)^(n-h/2)+(2:ℝ)^(n-h))
  have hh : h ≤ n := mask_bit_set_card_le n e
  have hlabel (ab : ℕ × ℕ) (_hab : ab ∈ S) :
      highXorPattern n tag e ab ∈ submaskTargets n e := by
    apply Finset.mem_filter.mpr
    unfold highXorPattern
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.and_le_left.trans_lt (Nat.mod_lt _ (by positivity))
    · rw [Nat.and_assoc, Nat.and_self]
  have hcount : S.card = ∑ z ∈ submaskTargets n e, (G z).card :=
    Finset.card_eq_sum_card_fiberwise hlabel
  have hf (z : ℕ) : ((G z).card:ℝ) ≤ C := by
    have hc := high_xor_pattern_count n δ ε tag tag' e z (G z) hδ hε
      (fun ab hab => hbox ab (Finset.mem_filter.mp hab).1)
      (fun ab hab => hevent ab (Finset.mem_filter.mp hab).1)
      (fun ab hab => (Finset.mem_filter.mp hab).2)
    exact hc.trans (dyadic_high_pattern_bound n h (taggedMaskTargets n tag e z).card
      hh (tagged_mask_targets_card_le n tag e z))
  have hcountR : (S.card:ℝ) = ∑ z ∈ submaskTargets n e, ((G z).card:ℝ) := by
    exact_mod_cast hcount
  have hp : ((submaskTargets n e).card:ℝ) ≤ (2:ℝ)^h := by
    exact_mod_cast submask_targets_card_le n e
  have htotal : (S.card:ℝ) ≤ 16*((2:ℝ)^((h+1)/2)+1)*(2:ℝ)^n := by
    calc
      _ = ∑ z ∈ submaskTargets n e, ((G z).card:ℝ) := hcountR
      _ ≤ ∑ _z ∈ submaskTargets n e, C := Finset.sum_le_sum (fun z _ => hf z)
      _ = ((submaskTargets n e).card:ℝ)*C := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2:ℝ)^h*C := mul_le_mul_of_nonneg_right hp (by dsimp only [C]; positivity)
      _ = _ := dyadic_high_pattern_sum n h hh
  exact_mod_cast htotal
-- CHECKPOINT

/-- Transfer a count on bounded natural pairs to the exact uniform key space. -/
theorem fin_pair_probability_of_nat_count (Q C : ℕ) (E : ℕ × ℕ → Prop)
    (hcount : ∀ S : Finset (ℕ × ℕ),
      (∀ ab ∈ S, ab.1 < Q ∧ ab.2 < Q) → (∀ ab ∈ S, E ab) → S.card ≤ C) :
    uniformProb (fun ab : Fin Q × Fin Q => E (ab.1.val, ab.2.val)) ≤ (C:ℚ≥0)/(Q:ℚ≥0)^2 := by
  classical
  let S := Finset.univ.filter (fun ab : Fin Q × Fin Q => E (ab.1.val, ab.2.val))
  let f : Fin Q × Fin Q → ℕ × ℕ := fun ab => (ab.1.val, ab.2.val)
  have hf : Function.Injective f := by
    intro a b he
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))
  have hc := hcount (S.image f)
    (by
      intro ab hab
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hab
      exact ⟨k.1.isLt, k.2.isLt⟩)
    (by
      intro ab hab
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hab
      exact (Finset.mem_filter.mp hk).2)
  rw [Finset.card_image_of_injective _ hf] at hc
  unfold uniformProb
  change (S.card:ℚ≥0)/(Fintype.card (Fin Q × Fin Q):ℚ≥0) ≤ _
  rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, ← pow_two]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
-- CHECKPOINT

/-- PROOF2 Lemma 4.2 in the exact finite-uniform probability convention. -/
theorem high_xor_quadratic_probability (n δ ε tag tag' e : ℕ)
    (hδ : 0 < δ ∧ δ < 2^n) (hε : 0 < ε ∧ ε < 2^n) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      highXorEventNat n δ ε tag tag' e (ab.1.val, ab.2.val)) ≤
      16*((2:ℚ≥0)^(((maskBitSet n e).card+1)/2)+1)/(2:ℚ≥0)^n := by
  have hc := fin_pair_probability_of_nat_count (2^n)
    (16*(2^(((maskBitSet n e).card+1)/2)+1)*2^n) (highXorEventNat n δ ε tag tag' e)
    (fun S hb he => high_xor_quadratic_count n δ ε tag tag' e S hδ hε hb he)
  calc
    _ ≤ (16*((2:ℚ≥0)^(((maskBitSet n e).card+1)/2)+1)*(2:ℚ≥0)^n)/
        ((2:ℚ≥0)^n)^2 := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hc
    _ = _ := by field_simp
-- CHECKPOINT

/-- The same high-ENH quadratic bound on the literal 64-bit word operands. -/
theorem high_xor_quadratic_probability_word (δ ε tag tag' e : ℕ)
    (hδ : 0 < δ ∧ δ < q) (hε : 0 < ε ∧ ε < q) :
    uniformProb (fun ab : Word × Word =>
      highXorEventNat 64 δ ε tag tag' e (ab.1.toNat, ab.2.toNat)) ≤
      16*((2:ℚ≥0)^(((maskBitSet 64 e).card+1)/2)+1)/q := by
  let equiv : (Fin (2^64) × Fin (2^64)) ≃ (Word × Word) :=
    Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv equiv]
  exact high_xor_quadratic_probability 64 δ ε tag tag' e hδ hε
-- CHECKPOINT

end ProvenHashes.UMASH
