import ProvenHashes.UMASHPHPrefix
import ProvenHashes.UMASHPatterns

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

/-- Once the lower bits are known, subtraction and XOR determine the same next bit. -/
theorem xor_sub_prefix_step (j x y x' y' : ℕ)
    (hx : x%2^j = x'%2^j) (hy : y%2^j = y'%2^j)
    (hd : Int.ModEq ((2:ℤ)^(j+1)) ((x:ℤ)-y) ((x':ℤ)-y')) :
    (x ^^^ y)%2^(j+1) = (x' ^^^ y')%2^(j+1) := by
  let d := x ^^^ y
  let d' := x' ^^^ y'
  have hp : d%2^j = d'%2^j := by
    dsimp only [d, d']
    rw [Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, hx, hy]
  have hap : (x &&& d)%2^j = (x' &&& d')%2^j := by
    rw [Nat.and_mod_two_pow, Nat.and_mod_two_pow, hx, hp]
  have ha : Int.ModEq ((2:ℤ)^j) (x &&& d : ℕ) (x' &&& d' : ℕ) := by
    exact_mod_cast Int.natCast_modEq_iff.mpr hap
  have ha2 : Int.ModEq ((2:ℤ)^(j+1)) (2*(x &&& d : ℕ)) (2*(x' &&& d' : ℕ)) := by
    convert ha.mul_left' (c := 2) using 1 <;> ring
  have hsx : 2*(x &&& d : ℕ)-((x:ℤ)-y) = (d:ℤ) := by
    have h := xor_signed_difference x y
    change (x:ℤ)-y = 2*(x &&& d : ℕ)-(d:ℤ) at h
    omega
  have hsy : 2*(x' &&& d' : ℕ)-((x':ℤ)-y') = (d':ℤ) := by
    have h := xor_signed_difference x' y'
    change (x':ℤ)-y' = 2*(x' &&& d' : ℕ)-(d':ℤ) at h
    omega
  have hh := ha2.sub hd
  rw [hsx, hsy] at hh
  exact Int.natCast_modEq_iff.mp (by exact_mod_cast hh)
-- CHECKPOINT

theorem word_sub_intModEq (x y x' y' : Word) (h : x-y = x'-y') :
    Int.ModEq (q:ℤ) ((x.toNat:ℤ)-y.toNat) ((x'.toNat:ℤ)-y'.toNat) := by
  have hcast (a b : Word) : ((a-b).toNat : ZMod q) =
      (a.toNat : ZMod q)-(b.toNat : ZMod q) := by
    rw [BitVec.toNat_sub]
    change (((q-b.toNat+a.toNat)%q : ℕ) : ZMod q) = _
    have hb : b.toNat ≤ q := b.isLt.le
    rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hb, ZMod.natCast_self]
    ring
  have hh := congrArg (fun a : Word => (a.toNat : ZMod q)) h
  dsimp only at hh
  rw [hcast, hcast] at hh
  apply (ZMod.intCast_eq_intCast_iff _ _ q).mp
  simpa only [Int.cast_sub, Int.cast_natCast] using hh
-- CHECKPOINT

/-- Bit-by-bit reconstruction of a word from the difference of two causal outputs. -/
theorem word_sub_injective_of_prefix (f g : Word → Word)
    (hf : ∀ a b j, j ≤ 64 → a.toNat%2^j = b.toNat%2^j →
      (f a).toNat%2^j = (f b).toNat%2^j)
    (hg : ∀ a b j, j ≤ 64 → a.toNat%2^j = b.toNat%2^j →
      (g a).toNat%2^j = (g b).toNat%2^j)
    (hi : ∀ a b j, j ≤ 64 →
      ((f a).toNat ^^^ (g a).toNat)%2^j = ((f b).toNat ^^^ (g b).toNat)%2^j →
      a.toNat%2^j = b.toNat%2^j) : Function.Injective (fun a => f a-g a) := by
  intro a b he
  have hd := word_sub_intModEq (f a) (g a) (f b) (g b) he
  have hp : ∀ j, j ≤ 64 → a.toNat%2^j = b.toNat%2^j := by
    intro j
    induction j with
    | zero => intro _; simp only [pow_zero]; omega
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hdiv : (2:ℤ)^(j+1) ∣ (q:ℤ) := by
        exact_mod_cast (show (2:ℕ)^(j+1) ∣ q from pow_dvd_pow 2 hj)
      exact hi a b (j+1) hj (xor_sub_prefix_step j _ _ _ _
        (hf a b j (by omega) hprev) (hg a b j (by omega) hprev) (hd.of_dvd hdiv))
  apply BitVec.eq_of_toNat_eq
  simpa only [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hp 64 le_rfl
-- CHECKPOINT

def lowAffinePH (u delta mask k : Word) : Word :=
  mask ^^^ (split (clmul u (k ^^^ delta))).1

theorem lowAffinePH_preserves_prefix (u delta mask a b : Word) (j : ℕ) (hj : j ≤ 64)
    (h : a.toNat%2^j = b.toNat%2^j) :
    (lowAffinePH u delta mask a).toNat%2^j = (lowAffinePH u delta mask b).toNat%2^j := by
  have hk : (a ^^^ delta).toNat%2^j = (b ^^^ delta).toNat%2^j := by
    rw [BitVec.toNat_xor, BitVec.toNat_xor, Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, h]
  have hp := clmul_preserves_prefix u (a ^^^ delta) (b ^^^ delta) j hk
  simp only [lowAffinePH, BitVec.toNat_xor, split, BitVec.toNat_setWidth]
  rw [Nat.xor_mod_two_pow, Nat.xor_mod_two_pow,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj), Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj), hp]
-- CHECKPOINT

theorem lowAffinePH_xor (u v alpha beta M N k : Word) :
    lowAffinePH u alpha M k ^^^ lowAffinePH v beta N k =
      (split (clmul (u ^^^ v) k)).1 ^^^
        (M ^^^ N ^^^ (split (clmul u alpha)).1 ^^^ (split (clmul v beta)).1) := by
  simp only [lowAffinePH, clmul_xor_right, clmul_xor_left, split_xor, xorChunk]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

theorem lowAffinePH_xor_reflects_prefix (u v alpha beta M N a b : Word)
    (hd : (u ^^^ v).getLsbD 0 = true) (j : ℕ) (hj : j ≤ 64)
    (h : ((lowAffinePH u alpha M a).toNat ^^^ (lowAffinePH v beta N a).toNat)%2^j =
      ((lowAffinePH u alpha M b).toNat ^^^ (lowAffinePH v beta N b).toNat)%2^j) :
    a.toNat%2^j = b.toNat%2^j := by
  let C := M ^^^ N ^^^ (split (clmul u alpha)).1 ^^^ (split (clmul v beta)).1
  have ha (k : Word) : lowAffinePH u alpha M k ^^^ lowAffinePH v beta N k =
      (split (clmul (u ^^^ v) k)).1 ^^^ C := lowAffinePH_xor u v alpha beta M N k
  have hw : (lowAffinePH u alpha M a ^^^ lowAffinePH v beta N a).toNat%2^j =
      (lowAffinePH u alpha M b ^^^ lowAffinePH v beta N b).toNat%2^j := by
    simpa only [BitVec.toNat_xor] using h
  rw [ha a, ha b] at hw
  have hn : ((split (clmul (u ^^^ v) a)).1.toNat%2^j) ^^^ (C.toNat%2^j) =
      ((split (clmul (u ^^^ v) b)).1.toNat%2^j) ^^^ (C.toNat%2^j) := by
    simpa only [BitVec.toNat_xor, Nat.xor_mod_two_pow] using hw
  have he := congrArg (fun n => n ^^^ (C.toNat%2^j)) hn
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at he
  apply clmul_odd_reflects_prefix (u ^^^ v) a b hd j
  simpa only [split, BitVec.toNat_setWidth,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj)] using he
-- CHECKPOINT

/-- The signed low-word difference on an odd PH slice determines its free key. -/
theorem odd_ph_slice_difference_injective (u v alpha beta M N : Word)
    (hd : (u ^^^ v).getLsbD 0 = true) :
    Function.Injective (fun k => lowAffinePH u alpha M k-lowAffinePH v beta N k) := by
  apply word_sub_injective_of_prefix
  · exact lowAffinePH_preserves_prefix u alpha M
  · exact lowAffinePH_preserves_prefix v beta N
  · intro a b j hj h
    exact lowAffinePH_xor_reflects_prefix u v alpha beta M N a b hd j hj h
-- CHECKPOINT

def projectionDifferenceTargets : Finset Word :=
  (Finset.range 17).image (fun (j : ℕ) => (((((j:ℤ)-8)*(p:ℤ)) : ℤ) : Word))

theorem projected_word_sub_mem (x y : Word) (h : x.toNat%p = y.toNat%p) :
    x-y ∈ projectionDifferenceTargets := by
  obtain ⟨_,j,hj,he⟩ := (mem_maskPatterns_iff _ _).mp
    (congruent_pattern x.toNat y.toNat x.isLt y.isLt h)
  have hd : (x.toNat:ℤ)-y.toNat = ((j:ℤ)-8)*(p:ℤ) := by
    have hs := xor_signed_difference x.toNat y.toNat
    omega
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
  rw [← hd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  simp [BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat]
-- CHECKPOINT

theorem injective_word_difference_probability {K : Type*} [Fintype K]
    (f g : K → Word) (hi : Function.Injective (fun k => f k-g k)) :
    uniformProb (fun k => (f k).toNat%p = (g k).toNat%p) ≤
      (17:ℚ≥0)/(Fintype.card K : ℚ≥0) := by
  have hc : projectionDifferenceTargets.card ≤ 17 := by
    exact Finset.card_image_le.trans_eq (Finset.card_range 17)
  exact (injective_target_probability _ hi projectionDifferenceTargets _
    (fun k hk => projected_word_sub_mem (f k) (g k) hk)).trans
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity))
-- CHECKPOINT

/-- Lemma 5.2 on its free-word slice, including both arbitrary XOR offsets. -/
theorem odd_ph_low_probability (u v alpha beta M N : Word)
    (hd : (u ^^^ v).getLsbD 0 = true) :
    uniformProb (fun k : Word => (lowAffinePH u alpha M k).toNat%p =
      (lowAffinePH v beta N k).toNat%p) ≤ (17:ℚ≥0)/q := by
  have hw : Fintype.card Word = q :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin q)
  simpa only [hw] using injective_word_difference_probability
    (lowAffinePH u alpha M) (lowAffinePH v beta N)
    (odd_ph_slice_difference_injective u v alpha beta M N hd)
-- CHECKPOINT

end ProvenHashes.UMASH
