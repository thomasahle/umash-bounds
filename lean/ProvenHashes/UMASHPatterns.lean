import ProvenHashes.UMASHMaskCertificate
import ProvenHashes.UMASHMaskExact
import Mathlib.Data.Int.ModEq

namespace ProvenHashes.UMASH

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet

/-- The signed-bit identity underlying the mask-pattern certificate. -/
theorem xor_signed_difference (x y : ℕ) :
    (x : ℤ) - y = 2 * (x &&& (x ^^^ y) : ℕ) - (x ^^^ y : ℕ) := by
  suffices h : x + (x ^^^ y) = y + 2 * (x &&& (x ^^^ y)) by omega
  induction x using Nat.binaryRec generalizing y with
  | zero => simp
  | bit b x ih =>
    cases y using Nat.bitCasesOn with
    | bit c y =>
      have h := ih y
      simp only [Nat.xor_bit, Nat.land_bit]
      cases b <;> cases c <;>
        simp only [Bool.bne_false, Bool.bne_true,
          Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true,
          Nat.bit_false, Nat.bit_true] at * <;> omega
-- CHECKPOINT

def patternNumerator (d j : ℕ) : ℤ := (d : ℤ) + ((j : ℤ)-8)*(p : ℤ)

/-- Only the seventeen possible signed multiples of p are inspected. -/
def maskPatterns (d : ℕ) : Finset ℕ :=
  ((Finset.range 17).filter fun j =>
    0 ≤ patternNumerator d j ∧ patternNumerator d j % 2 = 0 ∧
    (patternNumerator d j / 2).toNat &&& d = (patternNumerator d j / 2).toNat).image
      (fun j => (patternNumerator d j / 2).toNat)

theorem mem_maskPatterns_iff (d t : ℕ) :
    t ∈ maskPatterns d ↔ t &&& d = t ∧
      ∃ j : ℕ, j < 17 ∧ (2 : ℤ)*t = (d : ℤ) + ((j : ℤ)-8)*(p : ℤ) := by
  simp only [maskPatterns, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨j, ⟨hj, hn, he, ht⟩, rfl⟩
    refine ⟨ht, j, hj, ?_⟩
    have hc : 0 ≤ patternNumerator d j / 2 := Int.ediv_nonneg hn (by decide)
    rw [Int.toNat_of_nonneg hc]
    change 2 * (patternNumerator d j / 2) = patternNumerator d j
    omega
  · rintro ⟨ht, j, hj, he⟩
    have hn : patternNumerator d j = 2*(t : ℤ) := he.symm
    refine ⟨j, ⟨hj, ?_, ?_, ?_⟩, ?_⟩ <;> simp [hn, ht]
-- CHECKPOINT

theorem congruent_pattern (x y : ℕ) (hx : x < q) (hy : y < q)
    (h : x % p = y % p) : x &&& (x ^^^ y) ∈ maskPatterns (x ^^^ y) := by
  rw [mem_maskPatterns_iff]
  refine ⟨by simp only [Nat.and_assoc, Nat.and_self], ?_⟩
  have hqx : x / p ≤ 8 := by norm_num [q, p] at *; omega
  have hqy : y / p ≤ 8 := by norm_num [q, p] at *; omega
  let j := x / p + 8 - y / p
  refine ⟨j, (Nat.sub_le _ _).trans_lt (by omega), ?_⟩
  have hxq := Nat.mod_add_div x p
  have hyq := Nat.mod_add_div y p
  have hj : (j : ℤ)-8 = (x / p : ℕ) - (y / p : ℕ) := by
    dsimp [j]
    rw [Nat.cast_sub (hqy.trans (Nat.le_add_left 8 (x/p)))]
    push_cast
    ring
  have hd := xor_signed_difference x y
  rw [hj]
  have he : (x : ℤ) - y = ((x / p : ℕ) - (y / p : ℕ) : ℤ)*(p : ℤ) := by
    rw [← h] at hyq
    exact_mod_cast (show (x : ℤ) - y = ((x / p : ℕ) - (y / p : ℕ) : ℤ)*(p : ℤ) by
      have ha : (x : ℤ) = (x % p : ℕ) + (p : ℤ)*(x / p : ℕ) := by exact_mod_cast hxq.symm
      have hb : (y : ℤ) = (x % p : ℕ) + (p : ℤ)*(y / p : ℕ) := by exact_mod_cast hyq.symm
      rw [ha, hb]; ring)
  omega
-- CHECKPOINT

theorem pattern_implies_congruent (x y : ℕ)
    (h : x &&& (x ^^^ y) ∈ maskPatterns (x ^^^ y)) : x % p = y % p := by
  obtain ⟨_, j, _, hj⟩ := (mem_maskPatterns_iff _ _).mp h
  have hd := xor_signed_difference x y
  apply Int.natCast_modEq_iff.mp
  apply Int.modEq_iff_dvd.mpr
  refine ⟨8-(j : ℤ), ?_⟩
  nlinarith [hd, hj]
-- CHECKPOINT

theorem congruent_iff_pattern (x y : ℕ) (hx : x < q) (hy : y < q) :
    x % p = y % p ↔ x &&& (x ^^^ y) ∈ maskPatterns (x ^^^ y) :=
  ⟨congruent_pattern x y hx hy, pattern_implies_congruent x y⟩
-- CHECKPOINT

end ProvenHashes.UMASH
