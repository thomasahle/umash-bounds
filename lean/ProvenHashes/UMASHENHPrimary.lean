import ProvenHashes.UMASHLowProjection

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem word_increment_factor (d : ℕ) (hd0 : d ≠ 0) (hdq : d < q) :
    ∃ r < 64, 2^r ∣ d ∧ (d/2^r)%2 = 1 := by
  let r := padicValNat 2 d
  have hd : 2^r ∣ d := pow_padicValNat_dvd
  have hr : r < 64 := by
    by_contra h
    have hqd : q ∣ d := (pow_dvd_pow 2 (by omega : 64 ≤ r)).trans hd
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd
    omega
  have ho : (d/2^r)%2 = 1 := by
    have hn : ¬2 ∣ d/2^r := by
      rintro ⟨z, hz⟩
      apply pow_succ_padicValNat_not_dvd (p := 2) hd0
      refine ⟨z, ?_⟩
      change d = 2^(r+1)*z
      calc
        d = 2^r*(d/2^r) := (Nat.mul_div_cancel' hd).symm
        _ = _ := by rw [hz, pow_succ]; ring
    have hm : (d/2^r)%2 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
    omega
  exact ⟨r, hr, hd, ho⟩
-- CHECKPOINT

/-- Select a nonzero increment of minimum valuation, allowing one zero increment. -/
theorem increment_orientation (δ ε : ℕ) (hδq : δ < q) (hεq : ε < q)
    (hne : δ ≠ 0 ∨ ε ≠ 0) :
    ∃ r < 64, 2^r ∣ δ ∧ 2^r ∣ ε ∧
      ((δ/2^r)%2 = 1 ∨ (ε/2^r)%2 = 1) := by
  by_cases hδ : δ = 0
  · obtain ⟨r, hr, hd, ho⟩ := word_increment_factor ε (by tauto) hεq
    exact ⟨r, hr, hδ ▸ dvd_zero _, hd, Or.inr ho⟩
  by_cases hε : ε = 0
  · obtain ⟨r, hr, hd, ho⟩ := word_increment_factor δ hδ hδq
    exact ⟨r, hr, hd, hε ▸ dvd_zero _, Or.inl ho⟩
  obtain ⟨r, hr, hdr, hor⟩ := word_increment_factor δ hδ hδq
  obtain ⟨s, hs, hes, hos⟩ := word_increment_factor ε hε hεq
  rcases le_total r s with hrs | hsr
  · exact ⟨r, hr, hdr, (pow_dvd_pow 2 hrs).trans hes, Or.inl hor⟩
  · exact ⟨s, hs, (pow_dvd_pow 2 hsr).trans hdr, hes, Or.inr hos⟩
-- CHECKPOINT

theorem enhProjectedEvent_swap (δ ε tag tag' ML MH : ℕ) (ab : Chunk) :
    enhProjectedEvent δ ε tag tag' ML MH ab ↔
      enhProjectedEvent ε δ tag tag' ML MH (ab.2,ab.1) := by
  simp only [enhProjectedEvent, enhHighNat, Nat.mul_comm]
-- CHECKPOINT

/-- The operand bound needs only distinct input data, with no valuation premise. -/
theorem enh_projected_probability_any (δ ε tag tag' ML MH : ℕ)
    (hδq : δ < q) (hεq : ε < q) (hne : δ ≠ 0 ∨ ε ≠ 0)
    (hML : ML < q) (hMH : MH < q) :
    uniformProb (enhProjectedEvent δ ε tag tag' ML MH) ≤ (5542:ℚ≥0)/q := by
  obtain ⟨r, hr, hδ, hε, ho⟩ := increment_orientation δ ε hδq hεq hne
  rcases ho with ho | ho
  · exact enh_projected_probability r δ ε tag tag' ML MH hr hδ hε ho hεq hML hMH
  · calc
      _ = uniformProb (fun ab : Chunk =>
          enhProjectedEvent ε δ tag tag' ML MH ((Equiv.prodComm Word Word) ab)) :=
        congrArg uniformProb (funext fun ab => propext
          (enhProjectedEvent_swap δ ε tag tag' ML MH ab))
      _ = uniformProb (enhProjectedEvent ε δ tag tag' ML MH) :=
        uniformProb_equiv (Equiv.prodComm Word Word) _
      _ ≤ _ := enh_projected_probability r ε δ tag tag' ML MH
        hr hε hδ ho hδq hML hMH
-- CHECKPOINT

/-- Transfer a literal masked ENH collision to the counted operand event. -/
theorem masked_enh_event_to_operands (key data data' M : Chunk) (tag tag' : Word)
    (he : project (xorChunk M (enh key data tag)) =
      project (xorChunk M (enh key data' tag'))) :
    enhProjectedEvent (data'.1-data.1).toNat (data'.2-data.2).toNat
      tag.toNat tag'.toNat M.1.toNat M.2.toNat (data.1+key.1,data.2+key.2) := by
  have hshift (a a' v : Word) :
      (a'+v).toNat = ((a+v).toNat+(a'-a).toNat)%q := by
    have h : a'+v = (a+v)+(a'-a) := by abel
    rw [h, BitVec.toNat_add]
    rfl
  have h1 := congrArg (fun v : Field × Field => v.1.val) he
  have h2 := congrArg (fun v : Field × Field => v.2.val) he
  simp only [project, ZMod.val_natCast] at h1 h2
  have hl := congrArg Prod.fst (enh_toNat key data tag)
  have hl' := congrArg Prod.fst (enh_toNat key data' tag')
  dsimp only at hl hl'
  change (M.1 ^^^ (enh key data tag).1).toNat%p =
    (M.1 ^^^ (enh key data' tag').1).toNat%p at h1
  rw [BitVec.toNat_xor, BitVec.toNat_xor, hl, hl', hshift data.1 data'.1 key.1,
    hshift data.2 data'.2 key.2] at h1
  change (M.2 ^^^ (enh key data tag).2).toNat%p =
    (M.2 ^^^ (enh key data' tag').2).toNat%p at h2
  rw [masked_enh_high_toNat, masked_enh_high_toNat,
    hshift data.1 data'.1 key.1, hshift data.2 data'.2 key.2] at h2
  exact ⟨h1, h2⟩
-- CHECKPOINT

/-- The literal ENH bound for any two distinct data chunks under uniform keys. -/
theorem masked_enh_probability (data data' M : Chunk) (tag tag' : Word)
    (hne : data ≠ data') :
    uniformProb (fun key : Chunk => project (xorChunk M (enh key data tag)) =
      project (xorChunk M (enh key data' tag'))) ≤ (5542:ℚ≥0)/q := by
  let δ := (data'.1-data.1).toNat
  let ε := (data'.2-data.2).toNat
  have hd : δ ≠ 0 ∨ ε ≠ 0 := by
    by_contra h
    have hδ : δ = 0 := by tauto
    have hε : ε = 0 := by tauto
    have h1 : data'.1-data.1 = 0 := BitVec.eq_of_toNat_eq hδ
    have h2 : data'.2-data.2 = 0 := BitVec.eq_of_toNat_eq hε
    exact hne (Prod.ext (sub_eq_zero.mp h1).symm (sub_eq_zero.mp h2).symm)
  let e : Chunk ≃ Chunk := Equiv.prodCongr (Equiv.addLeft data.1) (Equiv.addLeft data.2)
  calc
    _ ≤ uniformProb (fun key : Chunk =>
        enhProjectedEvent δ ε tag.toNat tag'.toNat M.1.toNat M.2.toNat (e key)) :=
      probability_mono (fun key he => masked_enh_event_to_operands key data data' M tag tag' he)
    _ = uniformProb (enhProjectedEvent δ ε tag.toNat tag'.toNat M.1.toNat M.2.toNat) :=
      uniformProb_equiv e _
    _ ≤ _ := enh_projected_probability_any δ ε tag.toNat tag'.toNat M.1.toNat M.2.toNat
      (data'.1-data.1).isLt (data'.2-data.2).isLt hd M.1.isLt M.2.isLt
-- CHECKPOINT

end ProvenHashes.UMASH
