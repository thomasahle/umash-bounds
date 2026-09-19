import ProvenHashes.UMASHShortProbability

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

/-- Dividing both the modulus and a multiple-valued target by the scale. -/
theorem scaled_natCast_eq_iff (R Q u v : ℕ) (hR : R ≠ 0) :
    ((R*u : ℕ) : ZMod (R*Q)) = ((R*v : ℕ) : ZMod (R*Q)) ↔
      (u : ZMod Q) = (v : ZMod Q) := by
  rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff]
  exact Nat.ModEq.mul_left_cancel_iff' hR
-- CHECKPOINT

/-- An affine map with invertible slope is uniform after dropping high digits.
The inverse slope is the modular inverse supplied by `unitOfCoprime`. -/
theorem fin_affine_probability (R Q a : ℕ) (hR : 0 < R) (hQ : 0 < Q)
    (ha : Nat.Coprime a Q) (c t : ZMod Q) :
    uniformProb (fun b : Fin (R*Q) => (a : ZMod Q)*(b.val : ZMod Q)+c = t) =
      1/(Q : ℚ≥0) := by
  letI : NeZero R := ⟨by omega⟩
  letI : NeZero Q := ⟨by omega⟩
  let e : Fin Q ≃ ZMod Q :=
    { toFun := fun b => b.val
      invFun := fun z => ⟨z.val, z.val_lt⟩
      left_inv := fun b => Fin.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt])
      right_inv := fun z => ZMod.natCast_zmod_val z }
  have hf : Function.Bijective (fun z : ZMod Q => (a : ZMod Q)*z+c) := by
    have hi : Function.Injective (fun z : ZMod Q => (a : ZMod Q)*z+c) := by
      intro x y h
      exact (ZMod.unitOfCoprime a ha).isUnit.mul_right_injective (add_right_cancel h)
    exact ⟨hi, Finite.surjective_of_injective hi⟩
  rw [← uniformProb_equiv finProdFinEquiv
    (fun b : Fin (R*Q) => (a : ZMod Q)*(b.val : ZMod Q)+c = t)]
  apply probability_prod_eq
  intro hi
  change uniformProb (fun lo : Fin Q =>
    (a : ZMod Q)*((lo.val+Q*hi.val : ℕ) : ZMod Q)+c = t) = _
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  change uniformProb (fun lo : Fin Q => (a : ZMod Q)*e lo+c = t) = _
  rw [uniformProb_equiv e (fun z => (a : ZMod Q)*z+c = t)]
  simpa only [ZMod.card] using probability_bijective_point _ hf t
-- CHECKPOINT

/-- Lemma 4.1: exact uniformity on the multiples of the minimum power of two. -/
theorem low_additive_distribution : LowAdditiveDistribution := by
  intro r δ ε hr hδ hε hodd t
  let R := 2^r
  let Q := 2^(64-r)
  have hR : 0 < R := by dsimp [R]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hq : q = R*Q := by
    dsimp [q, R, Q]
    rw [← pow_add, Nat.add_sub_of_le hr.le]
    norm_num
  have hd : R*(δ/R) = δ := Nat.mul_div_cancel' hδ
  have he : R*(ε/R) = ε := Nat.mul_div_cancel' hε
  have ha : Nat.Coprime (δ/R) Q :=
    (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd)).pow_right (64-r)
  apply probability_prod_eq
  intro A
  have ht (B : Word) :
      (δ : ZMod q)*(B.toNat : ZMod q)+(ε : ZMod q)*(A.toNat : ZMod q)+
          (δ : ZMod q)*(ε : ZMod q) = ((R*t.val : ℕ) : ZMod q) ↔
      ((δ/R : ℕ) : ZMod Q)*(B.toNat : ZMod Q)+
          ((ε/R*A.toNat+δ*(ε/R) : ℕ) : ZMod Q) = (t.val : ZMod Q) := by
    generalize htval : t.val = v
    have hn : δ*B.toNat+ε*A.toNat+δ*ε =
        R*((δ/R)*B.toNat+(ε/R*A.toNat+δ*(ε/R))) := by
      calc
        _ = (R*(δ/R))*B.toNat+(R*(ε/R))*A.toNat+δ*(R*(ε/R)) := by rw [hd, he]
        _ = _ := by ring
    simp only [← Nat.cast_mul, ← Nat.cast_add]
    rw [hn, hq, scaled_natCast_eq_iff R Q _ _ (by omega)]
  trans uniformProb (fun B : Word =>
    ((δ/R : ℕ) : ZMod Q)*(B.toNat : ZMod Q)+
      ((ε/R*A.toNat+δ*(ε/R) : ℕ) : ZMod Q) = (t.val : ZMod Q))
  · exact congrArg uniformProb (funext (fun B => propext (ht B)))
  let e : Word ≃ Fin (R*Q) := BitVec.equivFin.toEquiv.trans (finCongr hq)
  change uniformProb (fun B : Word =>
    ((δ/R : ℕ) : ZMod Q)*((e B).val : ZMod Q)+
      ((ε/R*A.toNat+δ*(ε/R) : ℕ) : ZMod Q) = (t.val : ZMod Q)) = _
  rw [uniformProb_equiv e
    (fun B => ((δ/R : ℕ) : ZMod Q)*(B.val : ZMod Q)+
      ((ε/R*A.toNat+δ*(ε/R) : ℕ) : ZMod Q) = (t.val : ZMod Q)),
    fin_affine_probability R Q (δ/R) hR hQ ha]
  change 1/(Q : ℚ≥0) = (R : ℚ≥0)/(q : ℚ≥0)
  rw [hq, Nat.cast_mul]
  have hRn : (R : ℚ≥0) ≠ 0 := by exact_mod_cast hR.ne'
  field_simp
-- CHECKPOINT

/-- Every possible additive difference is a multiple of the prescribed scale. -/
theorem low_additive_support (r δ ε : ℕ) (hr : r < 64)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (ab : Word × Word) :
    ∃ t : Fin (q/2^r),
      (δ : ZMod q)*(ab.2.toNat : ZMod q)+(ε : ZMod q)*(ab.1.toNat : ZMod q)+
        (δ : ZMod q)*(ε : ZMod q) = ((2^r*t.val : ℕ) : ZMod q) := by
  let R := 2^r
  have hR : 0 < R := by dsimp [R]; positivity
  have hRq : R ∣ q := pow_dvd_pow 2 hr.le
  have hq : R*(q/R) = q := Nat.mul_div_cancel' hRq
  have hQ : 0 < q/R := Nat.div_pos (Nat.le_of_dvd (by norm_num [q]) hRq) hR
  let n := (δ/R)*ab.2.toNat+(ε/R)*ab.1.toNat+δ*(ε/R)
  refine ⟨⟨n%(q/R), Nat.mod_lt _ hQ⟩, ?_⟩
  have hn : δ*ab.2.toNat+ε*ab.1.toNat+δ*ε = R*n := by
    dsimp [n]
    calc
      _ = (R*(δ/R))*ab.2.toNat+(R*(ε/R))*ab.1.toNat+δ*(R*(ε/R)) := by
        rw [Nat.mul_div_cancel' hδ, Nat.mul_div_cancel' hε]
      _ = _ := by ring
  simp only [← Nat.cast_mul, ← Nat.cast_add]
  rw [hn]
  apply (ZMod.natCast_eq_natCast_iff _ _ q).mpr
  change Nat.ModEq q (R*n) (R*(n%(q/R)))
  simpa only [hq] using
    (show Nat.ModEq (q/R) n (n%(q/R)) from (Nat.mod_mod n (q/R)).symm).mul_left' R
-- CHECKPOINT

/-- An arbitrary target either belongs to that support or has zero probability. -/
theorem low_additive_target_le (r δ ε : ℕ) (hr : r < 64)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (hodd : (δ/2^r)%2 = 1) (z : ZMod q) :
    uniformProb (fun ab : Word × Word =>
      (δ : ZMod q)*(ab.2.toNat : ZMod q)+(ε : ZMod q)*(ab.1.toNat : ZMod q)+
        (δ : ZMod q)*(ε : ZMod q) = z) ≤ ((2^r : ℕ) : ℚ≥0)/q := by
  classical
  let E := fun ab : Word × Word =>
    (δ : ZMod q)*(ab.2.toNat : ZMod q)+(ε : ZMod q)*(ab.1.toNat : ZMod q)+
      (δ : ZMod q)*(ε : ZMod q) = z
  change uniformProb E ≤ _
  by_cases h : ∃ ab, E ab
  · obtain ⟨ab, hab⟩ := h
    obtain ⟨t, ht⟩ := low_additive_support r δ ε hr hδ hε ab
    have hz : z = ((2^r*t.val : ℕ) : ZMod q) := hab.symm.trans ht
    simpa only [E, hz] using (low_additive_distribution r δ ε hr hδ hε hodd t).le
  · have hn (ab : Word × Word) : ¬E ab := fun he => h ⟨ab, he⟩
    have hfun : E = fun _ => False :=
      funext (fun ab => propext (iff_false_intro (hn ab)))
    rw [hfun]
    simp [uniformProb]
-- CHECKPOINT

end ProvenHashes.UMASH
