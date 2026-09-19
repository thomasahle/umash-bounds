import ProvenHashes.UMASHAdditiveProductCore

namespace ProvenHashes.UMASH
open scoped Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 2000
attribute [local irreducible] wordFintype uniformProb Finset.univ Finset.range Finset.filter Finset.card

def additiveProductTarget (δ ε : ℕ) (z : ℤ) (ab : Word × Word) : Prop :=
  Int.ModEq ((q:ℤ)^2)
    ((((ab.1.toNat+δ)%q : ℕ):ℤ)*((ab.2.toNat+ε)%q : ℕ)-
      (ab.1.toNat:ℤ)*ab.2.toNat) z
attribute [local irreducible] additiveProductTarget

/-- PROOF3 Lemma 5.3, as an exact count over the literal two-word key space. -/
theorem additive_product_target_count (δ ε : ℕ) (z : ℤ)
    (hδq : δ < q) (hδ0 : δ ≠ 0) (hεq : ε < q) :
    (Finset.univ.filter (additiveProductTarget δ ε z)).card ≤ q := by
  classical
  calc
    _ ≤ (Finset.range q).card := by
      apply event_card_le_targets _ (fun ab : Word × Word => ab.1.toNat)
      · intro ab _
        exact Finset.mem_range.mpr ab.1.isLt
      · intro a b ha hb hab
        unfold additiveProductTarget at ha hb
        have hA : a.1 = b.1 := BitVec.eq_of_toNat_eq hab
        rcases a with ⟨A,B₁⟩
        rcases b with ⟨A',B₂⟩
        dsimp only at hA
        subst A'
        refine Prod.ext rfl (BitVec.eq_of_toNat_eq ?_)
        exact wrapped_product_difference_unique q A.toNat ((A.toNat+δ)%q) ε B₁.toNat B₂.toNat
          (by norm_num [q]) A.isLt (Nat.mod_lt _ (by norm_num [q]))
          (wrapped_add_ne q A.toNat δ A.isLt hδq hδ0).symm hεq B₁.isLt B₂.isLt
          (ha.trans hb.symm)
    _ = q := Finset.card_range q
-- CHECKPOINT

theorem additive_product_target_probability (δ ε : ℕ) (z : ℤ)
    (hδq : δ < q) (hδ0 : δ ≠ 0) (hεq : ε < q) :
    uniformProb (additiveProductTarget δ ε z) ≤ (1:ℚ≥0)/q := by
  classical
  have hc := additive_product_target_count δ ε z hδq hδ0 hεq
  have hw : Fintype.card Word = q :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin q)
  unfold uniformProb
  calc
    _ ≤ (q:ℚ≥0)/(Fintype.card (Word × Word):ℚ≥0) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := by norm_num [Fintype.card_prod, hw, q]
-- CHECKPOINT

/-- Raw low equality and high XOR zero imply one full additive target. -/
theorem enh_zero_mask_product_target (Q A B A' B' tag tag' M : ℕ)
    (hlo : A*B%Q = A'*B'%Q)
    (hm : enhHighNat Q A B tag M ^^^ enhHighNat Q A' B' tag' M = 0) :
    Int.ModEq ((Q:ℤ)^2) ((A':ℤ)*B'-(A:ℤ)*B) (-(Q:ℤ)*((tag':ℤ)-tag)) := by
  have hu : (A*B/Q+tag)%Q = (A'*B'/Q+tag')%Q := by
    have hh : ((A*B/Q+tag)%Q) ^^^ ((A'*B'/Q+tag')%Q) = 0 := by
      simpa only [enhHighNat, ← hlo, xor_common_cancel] using hm
    have he := congrArg (fun v : ℕ => v ^^^ ((A'*B'/Q+tag')%Q)) hh
    simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using he
  have hH : Int.ModEq (Q:ℤ) ((A*B/Q:ℕ)+tag : ℕ) ((A'*B'/Q:ℕ)+tag' : ℕ) :=
    Int.natCast_modEq_iff.mpr hu
  have hmul := hH.mul_left' (c := (Q:ℤ))
  have hprod : (A':ℤ)*B'-(A:ℤ)*B =
      (Q:ℤ)*((A'*B'/Q:ℕ)-(A*B/Q:ℕ):ℤ) := by
    have h₁ : (A:ℤ)*B = (A*B%Q:ℕ)+(Q:ℤ)*(A*B/Q:ℕ) := by
      exact_mod_cast (Nat.mod_add_div (A*B) Q).symm
    have h₂ : (A':ℤ)*B' = (A'*B'%Q:ℕ)+(Q:ℤ)*(A'*B'/Q:ℕ) := by
      exact_mod_cast (Nat.mod_add_div (A'*B') Q).symm
    rw [h₁,h₂,hlo]
    ring
  apply Int.modEq_iff_dvd.mpr
  rw [hprod, pow_two]
  convert dvd_neg.mpr hmul.dvd using 1 <;> push_cast <;> ring
-- CHECKPOINT

end ProvenHashes.UMASH
