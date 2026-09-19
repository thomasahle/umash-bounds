import ProvenHashes.UMASHPHENHAlgebra

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet

def lowRawTarget (seed : Word) (x y : Block) (u v : ℕ) (K : Fin 17 → Chunk) : Prop :=
  (rawPrimaryMask (keyPairsEquiv.symm K) seed x y).1.toNat = u ∧
    (rawSecondaryMask (keyPairsEquiv.symm K) seed x y).1.toNat = v

/-- A prescribed pair of raw low masks has the product PH/ENH bound, over
their two distinct key-pair coordinates. -/
theorem phenh_low_raw_target_probability (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (he : enhChanges x y = 2)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hr : r = enhValuation x y) (hr1 : 1 ≤ r) (hr64 : r ≤ 64)
    (u v : ℕ) (hu : 2^r ∣ u) (hv : 2^r ∣ v) :
    uniformProb (lowRawTarget seed x y u v) ≤
      2^r*lowTargetK r (phenhENHMask (x.chunks.length-(i+1)) u v)/q^2 := by
  let ip : Fin 17 := ⟨i, by omega⟩
  let ie : Fin 17 := ⟨x.chunks.length-1, by omega⟩
  let s := x.chunks.length-(i+1)
  let e := phenhENHMask s u v
  let P (w : Chunk) : Prop :=
    (ph w (x.chunks.getD i (0,0))).1 ^^^ (ph w (y.chunks.getD i (0,0))).1 = phenhPHMask s u v
  let Q (w : Chunk) : Prop :=
    (enh w (lastChunk x) (blockTag seed x)).1 ^^^
      (enh w (lastChunk y) (blockTag seed y)).1 = BitVec.ofNat 64 e
  have hij : ip ≠ ie := by
    intro h
    have hh := congrArg Fin.val h
    change i = x.chunks.length-1 at hh
    omega
  have hinput := single_ph_input_facts x y hc hs he i hi ho
  have hP : uniformProb P ≤ ((2^r:ℕ):ℚ≥0)/q :=
    ph_low_xor_target_probability _ _ _ hinput.1 hinput.2.1 r (hr.trans hinput.2.2.symm)
  obtain ⟨hne1,hne2⟩ := enhChanges_two_words x y he
  have heq : e < 2^64 := (BitVec.ofNat 64 u ^^^ phenhPHMask s u v).isLt
  have hed : 2^r ∣ e := phenhENHMask_dvd s r u v hr64 hu hv
  have hQ : uniformProb Q ≤ lowTargetK r e/q := by
    have h := enh_low_xor_target_probability (lastChunk x) (lastChunk y)
      (blockTag seed x) (blockTag seed y) (BitVec.ofNat 64 e) hne1 hne2 r hr hr1
      (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt heq] using hed)
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt heq] using h
  have hm : uniformProb (lowRawTarget seed x y u v) ≤
      uniformProb (fun K : Fin 17 → Chunk => P (K ip) ∧ Q (K ie)) := by
    apply probability_mono
    intro K hK
    have ht := single_ph_low_targets (keyPairsEquiv.symm K) seed x y hc i hi ho u v hK.1 hK.2
    simpa only [P, Q, ip, ie, s, e, blockPHDelta, blockENHDelta, xorChunk,
      keyPair_of_pairs K i (by omega), keyPair_of_pairs K (x.chunks.length-1) (by omega)] using ht
  calc
    _ ≤ uniformProb (fun K : Fin 17 → Chunk => P (K ip) ∧ Q (K ie)) := hm
    _ ≤ (((2^r:ℕ):ℚ≥0)/q)*(lowTargetK r e/q) :=
      probability_distinct_coordinates_le ip ie hij P Q _ _ hP hQ
    _ = _ := by simp only [Nat.cast_pow, Nat.cast_ofNat]; ring
-- CHECKPOINT

attribute [local irreducible] lowTargetK highTargetK twistLowWeight twistHighWeight
  phenhPHMask phenhENHMask phShuffleInverse

/-- PROOF2 (21) for the actual joint block event, including the conditional
low twisting weight. The masks are a union inside this single valuation case. -/
theorem phenh_low_ledger_bound (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (he : enhChanges x y = 2)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hr : r = enhValuation x y) (hr1 : 1 ≤ r) (hr64 : r ≤ 64) :
    uniformProb (jointEvent seed x y) ≤ phenhLowLedger r (x.chunks.length-(i+1))/q^2 := by
  let s := x.chunks.length-(i+1)
  let E (K : Fin 17 → Chunk) := jointEvent seed x y (keyPairsEquiv.symm K)
  let F (t : ℕ × ℕ) := lowRawTarget seed x y t.1 t.2
  let T := valuationMasks r ×ˢ valuationMasks r
  let C (t : ℕ × ℕ) : ℚ≥0 := 2^r*lowTargetK r (phenhENHMask s t.1 t.2)/q^2
  let W (t : ℕ × ℕ) := twistLowWeight t.2
  have hcover (K : Fin 17 → Chunk) (hK : E K) : ∃ t ∈ T, F t K := by
    have hm := single_ph_joint_low_masks (keyPairsEquiv.symm K) seed x y hc hs i hi ho r hr hr64 hK
    exact ⟨((rawPrimaryMask (keyPairsEquiv.symm K) seed x y).1.toNat,
      (rawSecondaryMask (keyPairsEquiv.symm K) seed x y).1.toNat),
      Finset.mem_product.mpr hm, rfl, rfl⟩
  have hfixed (t : ℕ × ℕ) (_ht : t ∈ T) (K : Fin 17 → Chunk) (v : Chunk) :
      F t (Function.update K 16 v) ↔ F t K := by
    have hm := raw_masks_update_twist K seed x y hx hy v
    simp only [F, lowRawTarget, hm.1, hm.2]
  have hslice (t : ℕ × ℕ) (_ht : t ∈ T) (K : Fin 17 → Chunk) (hK : F t K) :
      uniformProb (fun v => E (Function.update K 16 v)) ≤ W t := by
    have hw := secondary_twist_low_weight K seed x y hx hy hc hs
    change uniformProb (fun v : Chunk =>
      (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) x seed).1.toNat%p =
      (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) y seed).1.toNat%p) ≤
      twistLowWeight (rawSecondaryMask (keyPairsEquiv.symm K) seed x y).1.toNat at hw
    rw [hK.2] at hw
    apply (probability_mono ?_).trans hw
    intro v hv
    have hp := congrArg (fun c : Field × Field => c.1.val) hv.2
    simpa only [project, ZMod.val_natCast] using hp
  have hcount (t : ℕ × ℕ) (ht : t ∈ T) : uniformProb (F t) ≤ C t := by
    have hm := Finset.mem_product.mp ht
    exact phenh_low_raw_target_probability seed x y hx hc hs he i hi ho r hr hr1 hr64 t.1 t.2
      (Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hm.1).2)
      (Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hm.2).2)
  rw [← uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)]
  calc
    _ ≤ ∑ t ∈ T, C t*W t := probability_partition_update_le E F T 16 C W hcover hfixed hslice hcount
    _ = _ := by
      have hsum (A B : Finset ℕ) (c d : ℚ≥0) (g : ℕ × ℕ → ℚ≥0) (w : ℕ → ℚ≥0) :
          (∑ t ∈ A ×ˢ B, (c*g t/d)*w t.2) =
            c*(∑ u ∈ A, ∑ v ∈ B, g (u,v)*w v)/d := by
        simp only [Finset.sum_product, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
      exact hsum (valuationMasks r) (valuationMasks r) (2^r) (q^2)
        (fun t => lowTargetK r (phenhENHMask s t.1 t.2)) twistLowWeight
-- CHECKPOINT

def highRawTarget (seed : Word) (x y : Block) (i u v : ℕ) (K : Fin 17 → Chunk) : Prop :=
  (blockPHDelta (keyPairsEquiv.symm K) x y i).1 = 0 ∧
  (blockENHDelta (keyPairsEquiv.symm K) seed x y).1 = 0 ∧
  (rawPrimaryMask (keyPairsEquiv.symm K) seed x y).2.toNat = u ∧
  (rawSecondaryMask (keyPairsEquiv.symm K) seed x y).2.toNat = v

/-- The high raw-mask target keeps both low constraints and the full PH
point bound. The impossible top-bit targets contribute exactly zero. -/
theorem phenh_high_raw_target_probability (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (he : enhChanges x y = 2)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) (u v : ℕ) :
    uniformProb (highRawTarget seed x y i u v) ≤
      if (phenhPHMask (x.chunks.length-(i+1)) u v).toNat < 2^63 then
        highTargetK (phenhENHMask (x.chunks.length-(i+1)) u v)/q^2 else 0 := by
  let ip : Fin 17 := ⟨i, by omega⟩
  let ie : Fin 17 := ⟨x.chunks.length-1, by omega⟩
  let s := x.chunks.length-(i+1)
  let e := phenhENHMask s u v
  by_cases htop : (phenhPHMask s u v).toNat < 2^63
  · rw [if_pos htop]
    let P (w : Chunk) : Prop :=
      xorChunk (ph w (x.chunks.getD i (0,0))) (ph w (y.chunks.getD i (0,0))) = (0,phenhPHMask s u v)
    let Q (w : Chunk) : Prop :=
      (enh w (lastChunk x) (blockTag seed x)).1 = (enh w (lastChunk y) (blockTag seed y)).1 ∧
      (enh w (lastChunk x) (blockTag seed x)).2 ^^^
        (enh w (lastChunk y) (blockTag seed y)).2 = BitVec.ofNat 64 e
    have hij : ip ≠ ie := by
      intro h
      have hh := congrArg Fin.val h
      change i = x.chunks.length-1 at hh
      omega
    have hinput := single_ph_input_facts x y hc hs he i hi ho
    have hP : uniformProb P ≤ (1:ℚ≥0)/q :=
      ph_xor_target_probability _ _ _ (fun h => hinput.1 (congrArg Prod.fst h))
    obtain ⟨hne1,hne2⟩ := enhChanges_two_words x y he
    have heq : e < 2^64 := by
      unfold e phenhENHMask
      exact (BitVec.ofNat 64 u ^^^ phenhPHMask s u v).isLt
    have hQ : uniformProb Q ≤ highTargetK e/q := by
      have h := enh_high_xor_target_probability (lastChunk x) (lastChunk y)
        (blockTag seed x) (blockTag seed y) (BitVec.ofNat 64 e) hne1 hne2
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt heq] using h
    have hm : uniformProb (highRawTarget seed x y i u v) ≤
        uniformProb (fun K : Fin 17 → Chunk => P (K ip) ∧ Q (K ie)) := by
      apply probability_mono
      intro K hK
      have ht := single_ph_high_targets (keyPairsEquiv.symm K) seed x y hc i hi ho u v hK.2.2.1 hK.2.2.2
      have hp : blockPHDelta (keyPairsEquiv.symm K) x y i = (0,phenhPHMask s u v) :=
        Prod.ext hK.1 ht.1
      have hqe : (enh (keyPair (keyPairsEquiv.symm K) (x.chunks.length-1)) (lastChunk x) (blockTag seed x)).1 =
          (enh (keyPair (keyPairsEquiv.symm K) (x.chunks.length-1)) (lastChunk y) (blockTag seed y)).1 :=
        BitVec.xor_eq_zero_iff.mp hK.2.1
      constructor
      · simpa only [P, ip, s, blockPHDelta, keyPair_of_pairs K i (by omega)] using hp
      · simpa only [Q, ie, s, e, blockENHDelta, xorChunk,
          keyPair_of_pairs K (x.chunks.length-1) (by omega)] using And.intro hqe ht.2
    calc
      _ ≤ uniformProb (fun K : Fin 17 → Chunk => P (K ip) ∧ Q (K ie)) := hm
      _ ≤ ((1:ℚ≥0)/q)*(highTargetK e/q) :=
        probability_distinct_coordinates_le ip ie hij P Q _ _ hP hQ
      _ = _ := by
        have hmul (a : ℚ≥0) : ((1:ℚ≥0)/q)*(a/q) = a/q^2 := by ring
        exact hmul _
  · rw [if_neg htop]
    have hz : highRawTarget seed x y i u v = (fun _ => False) := by
      funext K
      apply propext
      constructor
      · intro hK
        have ht := single_ph_high_targets (keyPairsEquiv.symm K) seed x y hc i hi ho u v hK.2.2.1 hK.2.2.2
        have hb := ph_high_xor_lt (keyPair (keyPairsEquiv.symm K) i)
          (x.chunks.getD i (0,0)) (y.chunks.getD i (0,0))
        change (blockPHDelta (keyPairsEquiv.symm K) x y i).2.toNat < 2^63 at hb
        rw [ht.1] at hb
        exact htop hb
      · exact False.elim
    have hfalse (K : Type) [Fintype K] : uniformProb (fun _ : K => False) = 0 := by
      simp [uniformProb]
    rw [hz, hfalse]
-- CHECKPOINT

/-- PROOF2 (22) for the literal joint event. Low-zero reduction is used only
here, at r ≥ 4, before the high target and twisting weights are multiplied. -/
theorem phenh_high_ledger_bound (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (he : enhChanges x y = 2)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hr : r = enhValuation x y) (hr4 : 4 ≤ r) (hr64 : r ≤ 64) :
    uniformProb (jointEvent seed x y) ≤ phenhHighLedger (x.chunks.length-(i+1))/q^2 := by
  let s := x.chunks.length-(i+1)
  let E (K : Fin 17 → Chunk) := jointEvent seed x y (keyPairsEquiv.symm K)
  let F (t : ℕ × ℕ) := highRawTarget seed x y i t.1 t.2
  let T := maskSet ×ˢ maskSet
  let C (t : ℕ × ℕ) : ℚ≥0 := if (phenhPHMask s t.1 t.2).toNat < 2^63 then
    highTargetK (phenhENHMask s t.1 t.2)/q^2 else 0
  let W (t : ℕ × ℕ) := twistHighWeight t.2
  have hcover (K : Fin 17 → Chunk) (hK : E K) : ∃ t ∈ T, F t K := by
    have hm := joint_event_raw_masks (keyPairsEquiv.symm K) seed x y hc hs hK
    have hz := single_ph_joint_low_zero (keyPairsEquiv.symm K) seed x y hc hs i hi ho r hr hr4 hr64 hK
    exact ⟨((rawPrimaryMask (keyPairsEquiv.symm K) seed x y).2.toNat,
      (rawSecondaryMask (keyPairsEquiv.symm K) seed x y).2.toNat),
      Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm.1).2, (Finset.mem_product.mp hm.2).2⟩,
      hz.1, hz.2, rfl, rfl⟩
  have hfixed (t : ℕ × ℕ) (_ht : t ∈ T) (K : Fin 17 → Chunk) (v : Chunk) :
      F t (Function.update K 16 v) ↔ F t K := by
    have hm := raw_masks_update_twist K seed x y hx hy v
    have hki : keyPair (keyPairsEquiv.symm (Function.update K 16 v)) i =
        keyPair (keyPairsEquiv.symm K) i := by
      rw [keyPair_of_pairs _ i (by omega), keyPair_of_pairs _ i (by omega)]
      apply Function.update_of_ne
      intro h
      have hh := congrArg Fin.val h
      change i = 16 at hh
      omega
    have hke : keyPair (keyPairsEquiv.symm (Function.update K 16 v)) (x.chunks.length-1) =
        keyPair (keyPairsEquiv.symm K) (x.chunks.length-1) := by
      rw [keyPair_of_pairs _ _ (by omega), keyPair_of_pairs _ _ (by omega)]
      apply Function.update_of_ne
      intro h
      have hh := congrArg Fin.val h
      change x.chunks.length-1 = 16 at hh
      omega
    simp only [F, highRawTarget, hm.1, hm.2, blockPHDelta, blockENHDelta, hki, hke]
  have hslice (t : ℕ × ℕ) (_ht : t ∈ T) (K : Fin 17 → Chunk) (hK : F t K) :
      uniformProb (fun v => E (Function.update K 16 v)) ≤ W t := by
    have hw := secondary_twist_high_weight K seed x y hx hy hc hs
    change uniformProb (fun v : Chunk =>
      (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) x seed).2.toNat%p =
      (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) y seed).2.toNat%p) ≤
      twistHighWeight (rawSecondaryMask (keyPairsEquiv.symm K) seed x y).2.toNat at hw
    rw [hK.2.2.2] at hw
    apply (probability_mono ?_).trans hw
    intro v hv
    have hp := congrArg (fun c : Field × Field => c.2.val) hv.2
    simpa only [project, ZMod.val_natCast] using hp
  have hcount (t : ℕ × ℕ) (_ht : t ∈ T) : uniformProb (F t) ≤ C t :=
    phenh_high_raw_target_probability seed x y hx hc hs he i hi ho t.1 t.2
  rw [← uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)]
  calc
    _ ≤ ∑ t ∈ T, C t*W t := probability_partition_update_le E F T 16 C W hcover hfixed hslice hcount
    _ = _ := by
      have hsum (A B : Finset ℕ) (d : ℚ≥0) (P : ℕ × ℕ → Prop)
          (g : ℕ × ℕ → ℚ≥0) (w : ℕ → ℚ≥0) :
          (∑ t ∈ A ×ˢ B, (if P t then g t/d else 0)*w t.2) =
            (∑ u ∈ A, ∑ v ∈ B, if P (u,v) then g (u,v)*w v else 0)/d := by
        simp only [Finset.sum_product, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> ring
      simpa only [T, C, W, phenhHighLedger, s] using
        hsum maskSet maskSet (q^2) (fun t => (phenhPHMask s t.1 t.2).toNat < 2^63)
          (fun t => highTargetK (phenhENHMask s t.1 t.2)) twistHighWeight
-- CHECKPOINT

/-- PROOF2 Lemma 6.1 is now a closed theorem on the literal block model.
The four valuation regimes are separate cases, never a union over r or s. -/
theorem phenh_joint_ledger_reduction : PHENHJointLedgerReduction := by
  intro seed x y hx hy hc hs hp he hr hr63
  have hxlen : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  have hylen : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
  obtain ⟨i,hi,_hne,ho⟩ := phDiffCount_one_index x y hc hp
  refine ⟨x.chunks.length-(i+1), by omega, by omega, ?_⟩
  split_ifs with hv
  · exact phenh_low_ledger_bound seed x y hxlen hylen hc hs he i hi ho
      (enhValuation x y) rfl hr (by omega)
  · exact phenh_high_ledger_bound seed x y hxlen hylen hc hs he i hi ho
      (enhValuation x y) rfl (by omega) (by omega)
-- CHECKPOINT

end ProvenHashes.UMASH
