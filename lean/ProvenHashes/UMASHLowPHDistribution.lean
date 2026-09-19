import ProvenHashes.UMASHPHValuation

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

/-- Lemma 7.1: every multiple of 2^r has exactly 2^r preimages under the
literal truncated carry-less product. No scaled-width test is used. -/
theorem low_ph_distribution : LowPHDistribution := by
  intro d hd r hr z hz
  have hrt : r = (bitPolynomial d).natTrailingDegree :=
    hr.trans (bitPolynomial_trailing_eq_padic d hd).symm
  have hr64 : r < 64 := hrt ▸ (bitPolynomial_trailing d hd).1
  have hdr : 2^r ∣ d.toNat := hr ▸ pow_padicValNat_dvd
  let R := 2^r
  let Q := 2^(64-r)
  have hR : 0 < R := by dsimp [R]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  letI : NeZero R := ⟨by omega⟩
  letI : NeZero Q := ⟨by omega⟩
  have hq : q = R*Q := by
    dsimp [q, R, Q]
    rw [← pow_add, Nat.add_sub_of_le hr64.le]
    norm_num
  let e : (Fin R × Fin Q) ≃ Word := finProdFinEquiv.trans
    ((finCongr hq.symm).trans BitVec.equivFin.symm.toEquiv)
  have he (hi : Fin R) (lo : Fin Q) : (e (hi,lo)).toNat = lo.val+Q*hi.val := rfl
  have hdiv (k : Word) : R ∣ (split (clmul d k)).1.toNat :=
    clmul_low_divisible d k r hr64.le hdr
  have hb (w : Word) : w.toNat/R < Q := by
    apply (Nat.div_lt_iff_lt_mul hR).mpr
    have hw : w.toNat < q := w.isLt
    rw [hq] at hw
    simpa only [mul_comm] using hw
  let f (hi : Fin R) (lo : Fin Q) : Fin Q :=
    ⟨(split (clmul d (e (hi,lo)))).1.toNat/R, hb _⟩
  let t : Fin Q := ⟨z.toNat/R, hb z⟩
  have hinj (hi : Fin R) : Function.Injective (f hi) := by
    intro a b hab
    have heq := congrArg Fin.val hab
    change (split (clmul d (e (hi,a)))).1.toNat/R =
      (split (clmul d (e (hi,b)))).1.toNat/R at heq
    have hout : (split (clmul d (e (hi,a)))).1 = (split (clmul d (e (hi,b)))).1 := by
      apply BitVec.eq_of_toNat_eq
      calc
        _ = R*((split (clmul d (e (hi,a)))).1.toNat/R) := (Nat.mul_div_cancel' (hdiv _)).symm
        _ = R*((split (clmul d (e (hi,b)))).1.toNat/R) := congrArg (fun n => R*n) heq
        _ = _ := Nat.mul_div_cancel' (hdiv _)
    have hp := clmul_low_reflects_prefix d (e (hi,a)) (e (hi,b)) hd r hrt hout
    change (e (hi,a)).toNat%Q = (e (hi,b)).toNat%Q at hp
    rw [he hi a, he hi b, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hp
    exact Fin.ext hp
  have hevent (hi : Fin R) (lo : Fin Q) :
      (split (clmul d (e (hi,lo)))).1 = z ↔ f hi lo = t := by
    constructor
    · intro h
      apply Fin.ext
      change (split (clmul d (e (hi,lo)))).1.toNat/R = z.toNat/R
      rw [h]
    · intro h
      have heq := congrArg Fin.val h
      change (split (clmul d (e (hi,lo)))).1.toNat/R = z.toNat/R at heq
      apply BitVec.eq_of_toNat_eq
      calc
        _ = R*((split (clmul d (e (hi,lo)))).1.toNat/R) := (Nat.mul_div_cancel' (hdiv _)).symm
        _ = R*(z.toNat/R) := congrArg (fun n => R*n) heq
        _ = z.toNat := Nat.mul_div_cancel' hz
  calc
    _ = 1/(Q:ℚ≥0) := by
      rw [← uniformProb_equiv e (fun k : Word => (split (clmul d k)).1 = z)]
      apply probability_prod_eq
      intro hi
      have hf : (fun lo : Fin Q => (split (clmul d (e (hi,lo)))).1 = z) =
          (fun lo => f hi lo = t) := funext (fun lo => propext (hevent hi lo))
      rw [hf]
      simpa only [Fintype.card_fin] using probability_bijective_point (f hi)
        ⟨hinj hi, Finite.surjective_of_injective (hinj hi)⟩ t
    _ = ((2^r:ℕ):ℚ≥0)/q := by
      change 1/(Q:ℚ≥0) = (R:ℚ≥0)/(q:ℚ≥0)
      rw [hq, Nat.cast_mul]
      have hRn : (R:ℚ≥0) ≠ 0 := by exact_mod_cast hR.ne'
      field_simp
-- CHECKPOINT

end ProvenHashes.UMASH
