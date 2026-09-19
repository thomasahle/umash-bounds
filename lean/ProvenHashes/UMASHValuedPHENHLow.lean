import ProvenHashes.UMASHValuedPHENHAlgebra
import ProvenHashes.UMASHPHENHProbability

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet

theorem valued_phenh_low_raw_target_probability (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hval : ChunkValuation (lastChunk x) (lastChunk y) r) (hr1 : 1 ≤ r)
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
  have hinput := chunk_valuation_transfer _ _ _ _ r
    (single_ph_checksum_difference x y hc hs i hi ho) hval
  have hP : uniformProb P ≤ ((2^r:ℕ):ℚ≥0)/q :=
    ph_low_target_chunk_valuation _ _ _ r hinput
  have heq : e < 2^64 := (BitVec.ofNat 64 u ^^^ phenhPHMask s u v).isLt
  have hed : 2^r ∣ e := phenhENHMask_dvd s r u v hval.lt64.le hu hv
  have hQ : uniformProb Q ≤ lowTargetK r e/q := by
    have h := enh_low_target_chunk_valuation (lastChunk x) (lastChunk y)
      (blockTag seed x) (blockTag seed y) (BitVec.ofNat 64 e) r hval hr1
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
theorem valued_phenh_low_ledger_bound (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y)
    (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0))
    (r : ℕ) (hval : ChunkValuation (lastChunk x) (lastChunk y) r) (hr1 : 1 ≤ r) :
    uniformProb (jointEvent seed x y) ≤ phenhLowLedger r (x.chunks.length-(i+1))/q^2 := by
  let s := x.chunks.length-(i+1)
  let E (K : Fin 17 → Chunk) := jointEvent seed x y (keyPairsEquiv.symm K)
  let F (t : ℕ × ℕ) := lowRawTarget seed x y t.1 t.2
  let T := valuationMasks r ×ˢ valuationMasks r
  let C (t : ℕ × ℕ) : ℚ≥0 := 2^r*lowTargetK r (phenhENHMask s t.1 t.2)/q^2
  let W (t : ℕ × ℕ) := twistLowWeight t.2
  have hcover (K : Fin 17 → Chunk) (hK : E K) : ∃ t ∈ T, F t K := by
    have hm := valued_ph_joint_low_masks (keyPairsEquiv.symm K) seed x y hc hs i hi ho r hval hK
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
    exact valued_phenh_low_raw_target_probability seed x y hx hc hs i hi ho r hval hr1 t.1 t.2
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

end ProvenHashes.UMASH
