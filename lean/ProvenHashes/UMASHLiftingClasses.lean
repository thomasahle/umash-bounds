import ProvenHashes.UMASHENHFibre

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

/-- Integer form of the XOR addition identity, with no subtraction on naturals. -/
theorem xor_int_expand (x y : ℕ) :
    ((x ^^^ y : ℕ) : ℤ) = (x : ℤ) + y - 2*(x &&& y : ℕ) := by
  have h := xor_signed_difference x (x ^^^ y)
  simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h
  omega
-- CHECKPOINT

/-- The lifting function is affine in the individual input bits. -/
theorem lifting_function_affine (m t l : ℕ) (ht : t &&& m = t) :
    (m : ℤ)-2*((l &&& m) ^^^ t : ℕ) =
      ((m : ℤ)-2*t)-2*(l &&& m : ℕ)+4*(l &&& t : ℕ) := by
  rw [xor_int_expand]
  have ha : (l &&& m) &&& t = l &&& t := by
    rw [Nat.and_assoc, Nat.and_comm m t, ht]
  rw [ha]
  ring
-- CHECKPOINT

/-- Equal labels force agreement of the low r-2 bits of the patterns. -/
theorem lifting_label_pattern_prefix (r m t m' t' : ℕ) (hr : 2 ≤ r)
    (hm : m % 2^(r-1) = m' % 2^(r-1))
    (hc : Int.ModEq ((2:ℤ)^r) ((m:ℤ)-2*t) ((m':ℤ)-2*t')) :
    t % 2^(r-2) = t' % 2^(r-2) := by
  have hmI : Int.ModEq ((2:ℤ)^(r-1)) (m:ℤ) (m':ℤ) := by
    exact_mod_cast (Int.natCast_modEq_iff.mpr hm)
  have hcI := hc.of_dvd (pow_dvd_pow 2 (by omega : r-1 ≤ r))
  have hdiff : (2:ℤ)^(r-1) ∣ 2*((t':ℤ)-t) := by
    convert dvd_sub hmI.dvd hcI.dvd using 1 <;> ring
  have he : r-1 = (r-2)+1 := by omega
  rw [he, pow_succ, mul_comm ((2:ℤ)^(r-2)) 2] at hdiff
  have hd := Int.dvd_of_mul_dvd_mul_left (by norm_num : (2:ℤ) ≠ 0) hdiff
  exact Int.natCast_modEq_iff.mp (by exact_mod_cast (Int.modEq_iff_dvd.mpr hd))
-- CHECKPOINT

/-- PROOF3 Lemma 5.1, the direction needed to merge collision fibres.
It holds at every width r >= 2 and for every natural input, not just words. -/
theorem lifting_function_eq_of_label (r m t m' t' l : ℕ) (hr : 2 ≤ r)
    (ht : t &&& m = t) (ht' : t' &&& m' = t')
    (hm : m % 2^(r-1) = m' % 2^(r-1))
    (hc : Int.ModEq ((2:ℤ)^r) ((m:ℤ)-2*t) ((m':ℤ)-2*t')) :
    Int.ModEq ((2:ℤ)^r)
      ((m:ℤ)-2*((l &&& m) ^^^ t : ℕ))
      ((m':ℤ)-2*((l &&& m') ^^^ t' : ℕ)) := by
  rw [lifting_function_affine m t l ht, lifting_function_affine m' t' l ht']
  have htp := lifting_label_pattern_prefix r m t m' t' hr hm hc
  have hmp : (l &&& m) % 2^(r-1) = (l &&& m') % 2^(r-1) := by
    rw [Nat.and_mod_two_pow, Nat.and_mod_two_pow, hm]
  have htq : (l &&& t) % 2^(r-2) = (l &&& t') % 2^(r-2) := by
    rw [Nat.and_mod_two_pow, Nat.and_mod_two_pow, htp]
  have hmI : Int.ModEq ((2:ℤ)^(r-1)) ((l &&& m : ℕ):ℤ) ((l &&& m' : ℕ):ℤ) := by
    exact_mod_cast (Int.natCast_modEq_iff.mpr hmp)
  have htI : Int.ModEq ((2:ℤ)^(r-2)) ((l &&& t : ℕ):ℤ) ((l &&& t' : ℕ):ℤ) := by
    exact_mod_cast (Int.natCast_modEq_iff.mpr htq)
  have h2 : Int.ModEq ((2:ℤ)^r) (2*((l &&& m : ℕ):ℤ)) (2*((l &&& m' : ℕ):ℤ)) := by
    have hh := hmI.mul_left' (c := 2)
    convert hh using 1 <;> rw [← pow_succ'] <;> congr 1 <;> omega
  have h4 : Int.ModEq ((2:ℤ)^r) (4*((l &&& t : ℕ):ℤ)) (4*((l &&& t' : ℕ):ℤ)) := by
    have hh := htI.mul_left' (c := 4)
    convert hh using 1
    rw [show (4:ℤ) = 2^2 from by norm_num, ← pow_add]
    congr 1
    omega
  exact (hc.sub h2).add h4
-- CHECKPOINT

/-- The zero function class contains exactly the zero mask and pattern.
The modulus argument needs r >= 4; smaller r really permits other classes. -/
theorem maskPattern_zero_class (r m t : ℕ) (hr : 4 ≤ r)
    (ht : t ∈ maskPatterns m) (hc : ((m:ℤ)-2*t) % (2:ℤ)^r = 0) :
    m = 0 ∧ t = 0 := by
  obtain ⟨hsub,j,hj,hjt⟩ := (mem_maskPatterns_iff m t).mp ht
  have hd : (2:ℤ)^4 ∣ (p:ℤ)*((j:ℤ)-8) := by
    have hh := (pow_dvd_pow (2:ℤ) hr).trans (Int.dvd_of_emod_eq_zero hc)
    convert dvd_neg.mpr hh using 1 <;> nlinarith
  have hjd := odd_cancel_two_pow (p:ℤ) (by norm_num [p]) 4 ((j:ℤ)-8) hd
  have hje : (j:ℤ)-8 = 0 := by
    norm_num at hjd
    have hmod := Int.emod_eq_zero_of_dvd hjd
    omega
  have hmt : (m:ℤ) = 2*t := by rw [hje] at hjt; omega
  have hxor : t ^^^ m = t := by
    have hh := xor_int_expand t m
    rw [hsub, hmt] at hh
    omega
  have hz : m = 0 := by
    have hh := congrArg (fun x => t ^^^ x) hxor
    simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using hh
  exact ⟨hz, by omega⟩
-- CHECKPOINT

end ProvenHashes.UMASH
