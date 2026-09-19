import ProvenHashes.UMASHLowTargetDense

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- The two elementary terms already give a closed low-target theorem. -/
theorem low_xor_elementary_probability (δ ε r e : ℕ)
    (hδ : 0 < δ ∧ δ < q) (hε : 0 < ε ∧ ε < q)
    (hr : r = min (padicValNat 2 δ) (padicValNat 2 ε)) (hr1 : 1 ≤ r) (he : 2^r ∣ e) :
    uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
      min ((2:ℚ≥0)^r*2^((maskBitSet 64 e).card-(if e.testBit 63 then 1 else 0)))
        ((65:ℚ≥0)*2^(64-(maskBitSet 64 e).card))/q := by
  have hq : (0:ℚ≥0) < q := by norm_num [q]
  apply (le_div_iff₀ hq).mpr
  exact le_min ((le_div_iff₀ hq).mp (low_xor_sparse_probability δ ε r e hδ hε hr))
    ((le_div_iff₀ hq).mp (low_xor_dense_probability δ ε r e hδ hε hr hr1 he))
-- CHECKPOINT

/-- Submasks inherit all trailing zero bits of their containing mask. -/
theorem submask_power_dvd (r e z : ℕ) (he : 2^r ∣ e) (hz : z &&& e = z) : 2^r ∣ z := by
  apply Nat.dvd_of_mod_eq_zero
  rw [← hz, Nat.and_mod_two_pow, Nat.mod_eq_zero_of_dvd he, Nat.and_zero]
-- CHECKPOINT

/-- Every signed difference e-2z has exactly the valuation of a nonzero
XOR mask e. This includes negative differences and the top sign bit. -/
theorem signed_submask_exact_valuation (e z : ℕ) (he : 0 < e) (hz : z &&& e = z) :
    (2:ℤ)^(padicValNat 2 e) ∣ (e:ℤ)-2*z ∧
      ¬(2:ℤ)^(padicValNat 2 e+1) ∣ (e:ℤ)-2*z := by
  let v := padicValNat 2 e
  have heD : 2^v ∣ e := pow_padicValNat_dvd
  have hzD : 2^v ∣ z := submask_power_dvd v e z heD hz
  have heI : (2:ℤ)^v ∣ (e:ℤ) := by exact_mod_cast heD
  have hzI : (2:ℤ)^v ∣ (z:ℤ) := by exact_mod_cast hzD
  have hdouble : (2:ℤ)^(v+1) ∣ 2*(z:ℤ) := by
    rw [pow_succ, mul_comm ((2:ℤ)^v)]
    exact mul_dvd_mul_left 2 hzI
  refine ⟨heI.sub (dvd_mul_of_dvd_right hzI 2), ?_⟩
  intro hn
  have ht : (2:ℤ)^(v+1) ∣ (e:ℤ) := by
    simpa only [sub_add_cancel] using hn.add hdouble
  have htN : 2^(v+1) ∣ e := by exact_mod_cast ht
  exact pow_succ_padicValNat_not_dvd (p := 2) he.ne' htN
-- CHECKPOINT

/-- PROOF2 (18) as a literal ring identity in the transformed coordinate. -/
theorem low_coordinate_quadratic_identity {K : Type*} [CommRing K] (R a b A B : K) :
    a*(A*B) = -b*A^2+((a*B+b*A+R*a*b)-R*a*b)*A := by ring
-- CHECKPOINT

/-- Multiplying the new coordinate by R gives the actual product difference. -/
theorem low_coordinate_difference_identity {K : Type*} [CommRing K] (R a b A B : K) :
    (A+R*a)*(B+R*b)-A*B = R*(a*B+b*A+R*a*b) := by ring
-- CHECKPOINT

/-- The change (A,B) -> (A,aB+bA+Rab) is a bijection modulo any power of two
when a is odd. Its first coordinate is retained exactly. -/
theorem low_coordinate_bijective (n R a b : ℕ) (ha : a%2 = 1) :
    Function.Bijective (fun ab : ZMod (2^n) × ZMod (2^n) =>
      (ab.1,(a:ZMod (2^n))*ab.2+(b:ZMod (2^n))*ab.1+(R:ZMod (2^n))*a*b)) := by
  have hc : Nat.Coprime a (2^n) :=
    (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ha)).pow_right n
  have hi : Function.Injective (fun ab : ZMod (2^n) × ZMod (2^n) =>
      (ab.1,(a:ZMod (2^n))*ab.2+(b:ZMod (2^n))*ab.1+(R:ZMod (2^n))*a*b)) := by
    intro x y hxy
    have hA := congrArg Prod.fst hxy
    have hC := congrArg Prod.snd hxy
    dsimp only at hA hC
    apply Prod.ext hA
    rw [hA] at hC
    exact (ZMod.unitOfCoprime a hc).isUnit.mul_right_injective
      (add_right_cancel (add_right_cancel hC))
  exact ⟨hi, Finite.surjective_of_injective hi⟩
-- CHECKPOINT

/-- Every lift of the transformed coordinate has exact valuation v₂(e)-r.
The modulus may be any power of two; the coordinate may be signed. -/
theorem low_coordinate_exact_valuation (n r e z : ℕ) (C : ℤ)
    (he : 0 < e ∧ e < 2^n) (hz : z &&& e = z) (hr : r ≤ padicValNat 2 e)
    (hC : Int.ModEq ((2:ℤ)^n) ((2:ℤ)^r*C) ((e:ℤ)-2*z)) :
    (2:ℤ)^(padicValNat 2 e-r) ∣ C ∧
      ¬(2:ℤ)^(padicValNat 2 e-r+1) ∣ C := by
  let v := padicValNat 2 e
  have hv : v < n := (dyadic_increment_padic_factor n e he).1
  have hs := signed_submask_exact_valuation e z he.1 hz
  have hd : (2:ℤ)^(v+1) ∣ ((e:ℤ)-2*z)-(2:ℤ)^r*C :=
    (pow_dvd_pow (2:ℤ) (by omega : v+1 ≤ n)).trans hC.dvd
  have hdv : (2:ℤ)^v ∣ ((e:ℤ)-2*z)-(2:ℤ)^r*C :=
    (pow_dvd_pow (2:ℤ) (by omega : v ≤ v+1)).trans hd
  have hp : (2:ℤ)^v ∣ (2:ℤ)^r*C := by
    convert hs.1.sub hdv using 1 <;> ring
  have hnp : ¬(2:ℤ)^(v+1) ∣ (2:ℤ)^r*C := by
    intro h
    apply hs.2
    convert hd.add h using 1 <;> ring
  have hpow : (2:ℤ)^v = (2:ℤ)^r*2^(v-r) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  constructor
  · rw [hpow] at hp
    exact (mul_dvd_mul_iff_left (by positivity : (2:ℤ)^r ≠ 0)).mp hp
  · intro h
    apply hnp
    have hh := mul_dvd_mul_left ((2:ℤ)^r) h
    convert hh using 1
    rw [← pow_add]
    congr 1
    omega
-- CHECKPOINT

/-- Any common power of two in the quadratic coefficients lies strictly
below the selected mask bits. This is the part of (19) needed for division. -/
theorem low_coordinate_common_factor_bound (n r e z s : ℕ) (a b C : ℤ)
    (he : 0 < e ∧ e < 2^n) (hz : z &&& e = z) (hr : r ≤ padicValNat 2 e)
    (hC : Int.ModEq ((2:ℤ)^n) ((2:ℤ)^r*C) ((e:ℤ)-2*z))
    (hb : (2:ℤ)^s ∣ b) (hc : (2:ℤ)^s ∣ C-(2:ℤ)^r*a*b) :
    s+r ≤ padicValNat 2 e := by
  have hCd : (2:ℤ)^s ∣ C := by
    have hm : (2:ℤ)^s ∣ (2:ℤ)^r*a*b := dvd_mul_of_dvd_right hb _
    convert hc.add hm using 1 <;> ring
  have hval := low_coordinate_exact_valuation n r e z C he hz hr hC
  by_contra h
  have hs : padicValNat 2 e-r+1 ≤ s := by omega
  exact hval.2 ((pow_dvd_pow (2:ℤ) hs).trans hCd)
-- CHECKPOINT

/-- A literal low-XOR event fixes the scaled new coordinate modulo 2^n. -/
theorem low_coordinate_event_congruence (n r a b A B e : ℕ)
    (he : lowENHXor n (2^r*a) (2^r*b) A B = e) :
    Int.ModEq ((2:ℤ)^n)
      ((2:ℤ)^r*((a:ℤ)*B+(b:ℤ)*A+(2:ℤ)^r*a*b))
      ((e:ℤ)-2*(A*B%2^n &&& e:ℕ)) := by
  let L := A*B%2^n
  let L' := (A+2^r*a)*(B+2^r*b)%2^n
  have hh : L ^^^ L' = e := he
  have hd : (L':ℤ)-L = (e:ℤ)-2*(L &&& e:ℕ) := by
    have h := xor_signed_difference L L'
    rw [hh] at h
    omega
  have hL : Int.ModEq ((2^n:ℕ):ℤ) ((A*B:ℕ):ℤ) (L:ℤ) :=
    Int.natCast_modEq_iff.mpr (Nat.mod_mod _ _).symm
  have hL' : Int.ModEq ((2^n:ℕ):ℤ) (((A+2^r*a)*(B+2^r*b):ℕ):ℤ) (L':ℤ) :=
    Int.natCast_modEq_iff.mpr (Nat.mod_mod _ _).symm
  have hc := hL'.sub hL
  rw [hd] at hc
  push_cast at hc
  convert hc using 1 <;> ring
-- CHECKPOINT

/-- A scaled residue equation has at most R=2^r coordinate lifts modulo 2^n. -/
theorem scaled_coordinate_lift_count (n r : ℕ) (D : ℤ) (S : Finset ℕ) (hr : r ≤ n)
    (hbox : ∀ C ∈ S, C < 2^n)
    (hres : ∀ C ∈ S, Int.ModEq ((2:ℤ)^n) ((2:ℤ)^r*C) D) :
    S.card ≤ 2^r := by
  let Q := 2^(n-r)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hpow : 2^n = 2^r*Q := by dsimp only [Q]; rw [← pow_add, Nat.add_sub_of_le hr]
  have hpowI : (2:ℤ)^n = (2:ℤ)^r*(Q:ℤ) := by exact_mod_cast hpow
  calc
    _ ≤ (Finset.range (2^r)).card := by
      apply Finset.card_le_card_of_injOn (fun C : ℕ => C/Q)
      · intro C hC
        apply Finset.mem_range.mpr
        apply (Nat.div_lt_iff_lt_mul hQ).mpr
        simpa only [hpow] using hbox C hC
      · intro C hC C' hC' he
        have hm := (hres C hC).trans (hres C' hC').symm
        rw [hpowI] at hm
        have hc := Int.ModEq.mul_left_cancel' (by positivity : (2:ℤ)^r ≠ 0) hm
        have hcN : C%Q = C'%Q := Int.natCast_modEq_iff.mp hc
        have hd := Nat.mod_add_div C Q
        have hd' := Nat.mod_add_div C' Q
        dsimp only at he
        rw [hcN,he] at hd
        exact hd.symm.trans hd'
    _ = _ := Finset.card_range _
-- CHECKPOINT

end ProvenHashes.UMASH
