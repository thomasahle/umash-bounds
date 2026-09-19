import ProvenHashes.UMASHJointHighPH
import ProvenHashes.UMASHJointBody

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

theorem padicValNat_eq_of_odd_quotient (n r : ℕ) (hn : n ≠ 0)
    (hd : 2^r ∣ n) (ho : (n/2^r)%2 = 1) : padicValNat 2 n = r := by
  have hle : r ≤ padicValNat 2 n := (padicValNat_dvd_iff_le hn).mp hd
  apply Nat.le_antisymm _ hle
  by_contra hgt
  have hh : 2^(r+1) ∣ n := (padicValNat_dvd_iff_le hn).mpr (by omega)
  have hmul : 2^r*2 ∣ 2^r*(n/2^r) := by
    rw [Nat.mul_div_cancel' hd, ← pow_succ]
    exact hh
  have h2 : 2 ∣ n/2^r := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2^r)).mp hmul
  have hz := Nat.mod_eq_zero_of_dvd h2
  omega
-- CHECKPOINT

theorem chunk_difference_orientation (x y : Chunk) (hne : x ≠ y) :
    ∃ r < 64, 2^r ∣ (x.1 ^^^ y.1).toNat ∧ 2^r ∣ (x.2 ^^^ y.2).toNat ∧
      ((x.1 ≠ y.1 ∧ r = padicValNat 2 (x.1 ^^^ y.1).toNat) ∨
       (x.2 ≠ y.2 ∧ r = padicValNat 2 (x.2 ^^^ y.2).toNat)) := by
  have hnonzero : (x.1 ^^^ y.1).toNat ≠ 0 ∨ (x.2 ^^^ y.2).toNat ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    apply Prod.ext
    · apply BitVec.xor_eq_zero_iff.mp
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_zero] using h.1
    · apply BitVec.xor_eq_zero_iff.mp
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_zero] using h.2
  obtain ⟨r,hr,hx,hy,ho⟩ := increment_orientation (x.1 ^^^ y.1).toNat (x.2 ^^^ y.2).toNat
    (x.1 ^^^ y.1).isLt (x.2 ^^^ y.2).isLt hnonzero
  refine ⟨r,hr,hx,hy,?_⟩
  rcases ho with ho | ho
  · left
    have hn : (x.1 ^^^ y.1).toNat ≠ 0 := by intro h; simp [h] at ho
    refine ⟨?_, (padicValNat_eq_of_odd_quotient _ r hn hx ho).symm⟩
    intro h
    simp [h] at hn
  · right
    have hn : (x.2 ^^^ y.2).toNat ≠ 0 := by intro h; simp [h] at ho
    refine ⟨?_, (padicValNat_eq_of_odd_quotient _ r hn hy ho).symm⟩
    intro h
    simp [h] at hn
-- CHECKPOINT

theorem masked_ph_small_valuation_probability (x y M N : Chunk) (r : ℕ) (hr : r < 4)
    (hx : 2^r ∣ (x.1 ^^^ y.1).toNat) (hy : 2^r ∣ (x.2 ^^^ y.2).toNat)
    (hm : 2^r ∣ (M.1 ^^^ N.1).toNat)
    (ho : (x.1 ≠ y.1 ∧ r = padicValNat 2 (x.1 ^^^ y.1).toNat) ∨
      (x.2 ≠ y.2 ∧ r = padicValNat 2 (x.2 ^^^ y.2).toNat)) :
    uniformProb (fun k : Chunk => project (xorChunk M (ph k x)) =
      project (xorChunk N (ph k y))) ≤ (852:ℚ≥0)/q := by
  have hb : uniformProb (fun k : Chunk => project (xorChunk M (ph k x)) =
      project (xorChunk N (ph k y))) ≤ ((2^r*(valuationMasks r).card:ℕ):ℚ≥0)/q := by
    rcases ho with ho | ho
    · apply probability_prod_le
      intro fixed
      exact masked_ph_low_projection_right x y M N fixed r (by omega) ho.1 ho.2 hx hy hm
    · rw [← uniformProb_equiv (Equiv.prodComm Word Word)
        (fun k : Chunk => project (xorChunk M (ph k x)) = project (xorChunk N (ph k y)))]
      apply probability_prod_le
      intro fixed
      simpa only [ph, clmul_comm] using masked_ph_low_projection_right
        (x.2,x.1) (y.2,y.1) M N fixed r (by omega) ho.1 ho.2 hy hx hm
  have hc : 2^r*(valuationMasks r).card ≤ 852 := by
    interval_cases r <;> norm_num [valuationMasks_card_table.1, valuationMasks_card_table.2.1,
      valuationMasks_card_table.2.2.1, valuationMasks_card_table.2.2.2.1]
  exact hb.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity))
-- CHECKPOINT

end ProvenHashes.UMASH
