import ProvenHashes.UMASHENHFibre
import ProvenHashes.UMASHPatternCertificate
import ProvenHashes.UMASHProbability

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet maskPatterns wordFintype Finset.range Finset.product Finset.filter

def maskPatternPairs : Finset (Σ _ : ℕ, ℕ) := maskSet.sigma maskPatterns

theorem maskPatternPairs_card : maskPatternPairs.card = 2771 := by
  rw [maskPatternPairs, Finset.card_sigma]
  simpa only [patternWeight, valuationMasks, pow_zero, Nat.mod_one,
    eq_self_iff_true, Finset.filter_true] using patternWeight_table.1
-- CHECKPOINT

theorem enhHighNat_lt (w A B tag M : ℕ) (hM : M < 2^w) :
    enhHighNat (2^w) A B tag M < 2^w := by
  exact Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow hM (Nat.mod_lt _ (by positivity)))
    (Nat.mod_lt _ (by positivity))
-- CHECKPOINT

theorem event_card_le_targets {K V : Type*} [Fintype K]
    (E : K → Prop) (f : K → V) (T : Finset V)
    (hcover : ∀ k, E k → f k ∈ T)
    (hinj : ∀ a b, E a → E b → f a = f b → a = b) :
    (Finset.univ.filter E).card ≤ T.card := by
  classical
  apply Finset.card_le_card_of_injOn f
  · intro k hk
    exact hcover k (Finset.mem_filter.mp hk).2
  · intro a ha b hb hab
    exact hinj a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
-- CHECKPOINT

def enhLowEqualEvent (δ ε tag tag' M : ℕ) (ab : Word × Word) : Prop :=
  ab.1.toNat*ab.2.toNat % q = ((ab.1.toNat+δ)%q)*((ab.2.toNat+ε)%q) % q ∧
  enhHighNat q ab.1.toNat ab.2.toNat tag M % p =
    enhHighNat q ((ab.1.toNat+δ)%q) ((ab.2.toNat+ε)%q) tag' M % p

/-- Lemma 4.4: the collision event injects into (A, wrap, mask, pattern).
The two possible wraps are counted explicitly; tags and common masks are fixed. -/
theorem enh_low_equal_count (r δ ε tag tag' M : ℕ)
    (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hεq : ε < q) (hM : M < q) :
    (Finset.univ.filter (enhLowEqualEvent δ ε tag tag' M)).card ≤ q*5542 := by
  classical
  let X (ab : Word × Word) := enhHighNat q ab.1.toNat ab.2.toNat tag M
  let Y (ab : Word × Word) :=
    enhHighNat q ((ab.1.toNat+δ)%q) ((ab.2.toNat+ε)%q) tag' M
  let f (ab : Word × Word) : ℕ × (ℕ × (Σ _ : ℕ, ℕ)) :=
    (ab.1.toNat, ((ab.2.toNat+ε)/q, ⟨X ab ^^^ Y ab, X ab &&& (X ab ^^^ Y ab)⟩))
  have hX (ab : Word × Word) : X ab < q := enhHighNat_lt 64 _ _ _ _ hM
  have hY (ab : Word × Word) : Y ab < q := enhHighNat_lt 64 _ _ _ _ hM
  calc
    _ ≤ ((Finset.range q) ×ˢ ((Finset.range 2) ×ˢ maskPatternPairs)).card := by
      apply event_card_le_targets _ f
      · intro ab he
        refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ab.1.isLt,
          Finset.mem_product.mpr ⟨?_, ?_⟩⟩
        · apply Finset.mem_range.mpr
          change (ab.2.toNat+ε)/q < 2
          apply (Nat.div_lt_iff_lt_mul (by norm_num [q])).mpr
          have hbq : ab.2.toNat < q := ab.2.isLt
          exact (Nat.add_lt_add hbq hεq).trans_le (by omega)
        · apply Finset.mem_sigma.mpr
          exact ⟨congruent_xor_mem_maskSet _ _ (hX ab) (hY ab) he.2,
            congruent_pattern _ _ (hX ab) (hY ab) he.2⟩
      · intro a b haE hbE hab
        have hA : a.1 = b.1 := BitVec.eq_of_toNat_eq (congrArg Prod.fst hab)
        rcases a with ⟨A,B₁⟩
        rcases b with ⟨A',B₂⟩
        dsimp only at hA
        subst A'
        refine Prod.ext rfl ?_
        apply BitVec.eq_of_toNat_eq
        have hw := congrArg (fun v : ℕ × (ℕ × (Σ _ : ℕ, ℕ)) => v.2.1) hab
        have hp := congrArg (fun v : ℕ × (ℕ × (Σ _ : ℕ, ℕ)) => v.2.2) hab
        have hm := congrArg Sigma.fst hp
        have ht := congrArg (fun v : Σ _ : ℕ, ℕ => v.2) hp
        dsimp only [f] at hm ht
        apply enh_wrap_fibre_unique 64 r A.toNat δ ε B₁.toNat B₂.toNat tag tag' M
          (X (A,B₁) ^^^ Y (A,B₁)) (X (A,B₁) &&& (X (A,B₁) ^^^ Y (A,B₁)))
          hr hδ hε hodd B₁.isLt B₂.isLt
          (Nat.xor_lt_two_pow (hX _) (hY _)) hw haE.1 hbE.1 rfl hm.symm rfl
        change X (A,B₂) &&& (X (A,B₁) ^^^ Y (A,B₁)) = _
        rw [show X (A,B₁) ^^^ Y (A,B₁) = X (A,B₂) ^^^ Y (A,B₂) from hm]
        rw [hm] at ht
        exact ht.symm
    _ = q*5542 := by rw [Finset.card_product, Finset.card_product,
      Finset.card_range, Finset.card_range, maskPatternPairs_card]
-- CHECKPOINT

theorem enh_low_equal_probability (r δ ε tag tag' M : ℕ)
    (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hεq : ε < q) (hM : M < q) :
    uniformProb (enhLowEqualEvent δ ε tag tag' M) ≤ (5542:ℚ≥0)/q := by
  classical
  have hc := enh_low_equal_count r δ ε tag tag' M hr hδ hε hodd hεq hM
  have hw : Fintype.card Word = q :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin q)
  unfold uniformProb
  calc
    _ ≤ ((q*5542 : ℕ) : ℚ≥0)/(Fintype.card (Word × Word) : ℚ≥0) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := by norm_num [Fintype.card_prod, hw, q]
-- CHECKPOINT

end ProvenHashes.UMASH
