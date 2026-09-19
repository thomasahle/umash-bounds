import ProvenHashes.UMASHENHCount

namespace ProvenHashes.UMASH
open scoped Classical
set_option maxHeartbeats 2000000

/-- An odd linear coefficient makes a quadratic injective within each parity
class modulo every power of two. -/
theorem quadratic_odd_linear_parity_unique (n x y : ℕ) (b c d : ℤ)
    (hc : c%2 = 1) (hx : x < 2^n) (hy : y < 2^n) (hpar : x%2 = y%2)
    (he : Int.ModEq ((2:ℤ)^n)
      (b*(x:ℤ)^2+c*x+d) (b*(y:ℤ)^2+c*y+d)) : x = y := by
  have hp : (x:ℤ)%2 = (y:ℤ)%2 := by exact_mod_cast hpar
  have hs : ((x:ℤ)+y)%2 = 0 := by omega
  have hodd : (b*((x:ℤ)+y)+c)%2 = 1 := by
    rw [Int.add_emod, Int.mul_emod, hs, hc]
    norm_num
  have hd : (2:ℤ)^n ∣ (b*((x:ℤ)+y)+c)*((y:ℤ)-x) := by
    convert he.dvd using 1 <;> ring
  have hm : Int.ModEq ((2:ℤ)^n) (x:ℤ) (y:ℤ) :=
    Int.modEq_iff_dvd.mpr (odd_cancel_two_pow _ hodd n _ hd)
  have hn : x%2^n = y%2^n :=
    Int.natCast_modEq_iff.mp (by exact_mod_cast hm)
  simpa only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hn
-- CHECKPOINT

def quadraticRootEvent (n : ℕ) (b c d z : ℤ) (x : Fin (2^n)) : Prop :=
  Int.ModEq ((2:ℤ)^n) (b*(x.val:ℤ)^2+c*x.val+d) z
attribute [local irreducible] quadraticRootEvent

/-- The at-most-two-roots clause used in PROOF2 Lemma 5.1 and PROOF3
Lemma 3.1(c). The width and coefficients are unrestricted. -/
theorem quadratic_odd_linear_root_count (n : ℕ) (b c d z : ℤ) (hc : c%2 = 1) :
    (Finset.univ.filter (quadraticRootEvent n b c d z)).card ≤ 2 := by
  classical
  calc
    _ ≤ (Finset.range 2).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin (2^n) => x.val%2)
      · intro x _
        exact Finset.mem_range.mpr (Nat.mod_lt _ (by decide))
      · intro x hx y hy hpar
        have hx := (Finset.mem_filter.mp hx).2
        have hy := (Finset.mem_filter.mp hy).2
        unfold quadraticRootEvent at hx hy
        exact Fin.ext (quadratic_odd_linear_parity_unique n x.val y.val b c d hc
          x.isLt y.isLt hpar (hx.trans hy.symm))
    _ = 2 := Finset.card_range 2
-- CHECKPOINT

theorem quadratic_odd_linear_root_probability (n : ℕ) (b c d z : ℤ) (hc : c%2 = 1) :
    uniformProb (quadraticRootEvent n b c d z) ≤ (2:ℚ≥0)/2^n := by
  classical
  unfold uniformProb
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (quadratic_odd_linear_root_count n b c d z hc)) (by positivity)
-- CHECKPOINT

end ProvenHashes.UMASH
