import ProvenHashes.UMASHJointPrefixes

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet

theorem low_ph_target_le (d : Word) (hd : d ≠ 0) (r : ℕ)
    (hr : r = padicValNat 2 d.toNat) (z : Word) :
    uniformProb (fun k : Word => (split (clmul d k)).1 = z) ≤ ((2^r:ℕ):ℚ≥0)/q := by
  by_cases hz : 2^r ∣ z.toNat
  · exact (low_ph_distribution d hd r hr z hz).le
  have hrt : r = (bitPolynomial d).natTrailingDegree := hr.trans (bitPolynomial_trailing_eq_padic d hd).symm
  have hr64 : r < 64 := hrt ▸ (bitPolynomial_trailing d hd).1
  have hdiv : 2^r ∣ d.toNat := hr ▸ pow_padicValNat_dvd
  have he : (fun k : Word => (split (clmul d k)).1 = z) = (fun _ => False) := by
    funext k
    apply propext
    constructor
    · intro hk
      exact hz (hk ▸ clmul_low_divisible d k r hr64.le hdiv)
    · exact False.elim
  rw [he]
  simp [uniformProb]
-- CHECKPOINT

theorem low_affine_xor_target_probability (u v alpha beta M N t : Word)
    (hd : u ^^^ v ≠ 0) (r : ℕ) (hr : r = padicValNat 2 (u ^^^ v).toNat) :
    uniformProb (fun k : Word => lowAffinePH u alpha M k ^^^ lowAffinePH v beta N k = t) ≤
      ((2^r:ℕ):ℚ≥0)/q := by
  let C := M ^^^ N ^^^ (split (clmul u alpha)).1 ^^^ (split (clmul v beta)).1
  apply (probability_mono ?_).trans (low_ph_target_le (u ^^^ v) hd r hr (t ^^^ C))
  intro k hk
  rw [lowAffinePH_xor] at hk
  change (split (clmul (u ^^^ v) k)).1 ^^^ C = t at hk
  have he := congrArg (fun w : Word => w ^^^ C) hk
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using he
-- CHECKPOINT

theorem projected_low_prefix_probability {K : Type*} [Fintype K] (x y : K → Chunk)
    (r : ℕ) (c : ℚ≥0)
    (hpre : ∀ k, 2^r ∣ ((x k).1 ^^^ (y k).1).toNat)
    (hpoint : ∀ t : Word, uniformProb (fun k => (x k).1 ^^^ (y k).1 = t) ≤ c) :
    uniformProb (fun k => project (x k) = project (y k)) ≤ (valuationMasks r).card*c := by
  classical
  let T := valuationMasks r
  let E (t : ℕ) (k : K) := (x k).1 ^^^ (y k).1 = BitVec.ofNat 64 t
  calc
    _ ≤ uniformProb (fun k => ∃ t ∈ T, E t k) := by
      apply probability_mono
      intro k hk
      refine ⟨((x k).1 ^^^ (y k).1).toNat, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · simpa only [BitVec.toNat_xor] using
            (Finset.mem_product.mp (project_eq_mask_cover (x k) (y k) hk)).1
        · exact Nat.mod_eq_zero_of_dvd (hpre k)
      · simp [E]
    _ ≤ ∑ t ∈ T, uniformProb (E t) := probability_union_bound T E
    _ ≤ ∑ _t ∈ T, c := Finset.sum_le_sum (fun t _ => hpoint (BitVec.ofNat 64 t))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
-- CHECKPOINT

theorem masked_ph_low_prefix (x y M N k : Chunk) (r : ℕ) (hr : r ≤ 64)
    (hx : 2^r ∣ (x.1 ^^^ y.1).toNat) (hy : 2^r ∣ (x.2 ^^^ y.2).toNat)
    (hm : 2^r ∣ (M.1 ^^^ N.1).toNat) :
    2^r ∣ ((xorChunk M (ph k x)).1 ^^^ (xorChunk N (ph k y)).1).toNat := by
  apply (word_prefix_eq_iff_xor_dvd _ _ r).mp
  have hM := (word_prefix_eq_iff_xor_dvd M.1 N.1 r).mpr hm
  have hP := ph_low_prefix x y k r hr hx hy
  simp only [xorChunk, BitVec.toNat_xor, Nat.xor_mod_two_pow]
  rw [hM, hP]
-- CHECKPOINT

theorem masked_ph_low_projection_right (x y M N : Chunk) (fixed : Word)
    (r : ℕ) (hr64 : r < 64) (hne : x.1 ≠ y.1)
    (hr : r = padicValNat 2 (x.1 ^^^ y.1).toNat)
    (hx : 2^r ∣ (x.1 ^^^ y.1).toNat) (hy : 2^r ∣ (x.2 ^^^ y.2).toNat)
    (hm : 2^r ∣ (M.1 ^^^ N.1).toNat) :
    uniformProb (fun k : Word => project (xorChunk M (ph (fixed,k) x)) =
      project (xorChunk N (ph (fixed,k) y))) ≤
        ((2^r*(valuationMasks r).card:ℕ):ℚ≥0)/q := by
  have hcancel : (x.1 ^^^ fixed) ^^^ (y.1 ^^^ fixed) = x.1 ^^^ y.1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  have hd : (x.1 ^^^ fixed) ^^^ (y.1 ^^^ fixed) ≠ 0 := by
    rw [hcancel]
    exact fun h => hne (BitVec.xor_eq_zero_iff.mp h)
  have hp (t : Word) :
      uniformProb (fun k : Word => (xorChunk M (ph (fixed,k) x)).1 ^^^
        (xorChunk N (ph (fixed,k) y)).1 = t) ≤ ((2^r:ℕ):ℚ≥0)/q := by
    have hf (d mask : Chunk) (k : Word) :
        (xorChunk mask (ph (fixed,k) d)).1 = lowAffinePH (d.1 ^^^ fixed) d.2 mask.1 k := by
      simp only [xorChunk, ph, lowAffinePH]
      rw [BitVec.xor_comm k d.2]
    simp only [hf]
    exact low_affine_xor_target_probability _ _ _ _ _ _ t hd r (by simpa only [hcancel] using hr)
  have hb := projected_low_prefix_probability
    (fun k : Word => xorChunk M (ph (fixed,k) x)) (fun k => xorChunk N (ph (fixed,k) y))
    r (((2^r:ℕ):ℚ≥0)/q) (fun k => masked_ph_low_prefix x y M N (fixed,k) r hr64.le hx hy hm) hp
  convert hb using 1
  rw [Nat.cast_mul]
  ring
-- CHECKPOINT

end ProvenHashes.UMASH
