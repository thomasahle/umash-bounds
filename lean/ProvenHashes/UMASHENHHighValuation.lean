import ProvenHashes.UMASHENHCount
import ProvenHashes.UMASHMaskRefinements

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet

theorem congruent_equal_low_four (x y : ℕ) (hx : x < q) (hy : y < q)
    (hp : x%p = y%p) (h16 : x%16 = y%16) : x = y := by
  have hd := congruent_xor_mem_maskSet x y hx hy hp
  have hz : (x ^^^ y)%16 = 0 := by
    change (x ^^^ y)%2^4 = 0
    rw [Nat.xor_mod_two_pow, h16, Nat.xor_self]
  have hm : x ^^^ y ∈ maskSet.filter (fun d => d%16 = 0) :=
    Finset.mem_filter.mpr ⟨hd, hz⟩
  rw [maskSet_mod_sixteen, Finset.mem_singleton] at hm
  have h := congrArg (fun a => a ^^^ y) hm
  simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using h
-- CHECKPOINT

theorem wrapped_product_mod_sixteen (A B δ ε : ℕ) (hδ : 16 ∣ δ) (hε : 16 ∣ ε) :
    (A*B%q)%16 = (((A+δ)%q)*((B+ε)%q)%q)%16 := by
  have hq : 16 ∣ q := by norm_num [q]
  have ha : ((A+δ)%q)%16 = A%16 := by
    rw [Nat.mod_mod_of_dvd _ hq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hδ]
    simp only [Nat.add_zero, Nat.mod_mod]
  have hb : ((B+ε)%q)%16 = B%16 := by
    rw [Nat.mod_mod_of_dvd _ hq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hε]
    simp only [Nat.add_zero, Nat.mod_mod]
  rw [Nat.mod_mod_of_dvd _ hq, Nat.mod_mod_of_dvd _ hq]
  conv_rhs => rw [Nat.mul_mod, ha, hb]
  exact Nat.mul_mod _ _ _
-- CHECKPOINT

def enhProjectedEvent (δ ε tag tag' ML MH : ℕ) (ab : Word × Word) : Prop :=
  (ML ^^^ (ab.1.toNat*ab.2.toNat%q))%p =
    (ML ^^^ (((ab.1.toNat+δ)%q)*((ab.2.toNat+ε)%q)%q))%p ∧
  enhHighNat q ab.1.toNat ab.2.toNat tag MH % p =
    enhHighNat q ((ab.1.toNat+δ)%q) ((ab.2.toNat+ε)%q) tag' MH % p

theorem enh_projected_implies_low_equal (δ ε tag tag' ML MH : ℕ)
    (hδ : 16 ∣ δ) (hε : 16 ∣ ε) (hML : ML < q)
    (ab : Word × Word) (he : enhProjectedEvent δ ε tag tag' ML MH ab) :
    enhLowEqualEvent δ ε tag tag' MH ab := by
  refine ⟨?_, he.2⟩
  let L := ab.1.toNat*ab.2.toNat%q
  let L' := ((ab.1.toNat+δ)%q)*((ab.2.toNat+ε)%q)%q
  have hlo : L%16 = L'%16 := wrapped_product_mod_sixteen _ _ δ ε hδ hε
  have hxor : (ML ^^^ L)%16 = (ML ^^^ L')%16 := by
    change (ML ^^^ L)%2^4 = (ML ^^^ L')%2^4
    rw [Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, hlo]
  have heq := congruent_equal_low_four (ML ^^^ L) (ML ^^^ L')
    (Nat.xor_lt_two_pow hML (Nat.mod_lt _ (by norm_num [q])))
    (Nat.xor_lt_two_pow hML (Nat.mod_lt _ (by norm_num [q]))) he.1 hxor
  have h := congrArg (fun a => ML ^^^ a) heq
  simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using h
-- CHECKPOINT

/-- Primary ENH projection at every valuation r >= 4, for arbitrary tags and
both arbitrary common XOR offsets.  The event is on uniform operand words. -/
theorem enh_high_valuation_probability (r δ ε tag tag' ML MH : ℕ)
    (h4 : 4 ≤ r) (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hεq : ε < q) (hML : ML < q) (hMH : MH < q) :
    uniformProb (enhProjectedEvent δ ε tag tag' ML MH) ≤ (5542:ℚ≥0)/q := by
  have hd16 : 16 ∣ δ := (pow_dvd_pow 2 h4).trans hδ
  have he16 : 16 ∣ ε := (pow_dvd_pow 2 h4).trans hε
  exact (probability_mono (enh_projected_implies_low_equal δ ε tag tag' ML MH
    hd16 he16 hML)).trans
    (enh_low_equal_probability r δ ε tag tag' MH hr hδ hε hodd hεq hMH)
-- CHECKPOINT

end ProvenHashes.UMASH
