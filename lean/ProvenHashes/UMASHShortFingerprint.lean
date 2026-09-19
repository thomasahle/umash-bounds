import ProvenHashes.UMASHShortClosure
import ProvenHashes.UMASHJointProbability

/-! The short/short two-multiplier fingerprint branch. The two short noise
index ranges may overlap; the largest secondary index is nevertheless fresh
relative to the primary collision event. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem shortHash_secondary_eq_mixer (k : OHKey) (seed : Word) (m : Message) :
    shortHash k seed m true =
      shortFinish (shortPrepare (shortPack m) ^^^ (seed + keyWord k (m.length+4))) := by
  simp only [shortHash, ↓reduceIte, shortFinish, shortPrepare]
-- CHECKPOINT

theorem shortHash_secondary_noise_bijective (seed : Word) (m : Message)
    (hm : m.length+4 < 34) (k : OHKey) : Function.Bijective (fun v : Word =>
      shortHash (Function.update k ⟨m.length+4,hm⟩ v) seed m true) := by
  suffices hi : Function.Injective (fun v : Word =>
      shortHash (Function.update k ⟨m.length+4,hm⟩ v) seed m true) from
    ⟨hi, Finite.surjective_of_injective hi⟩
  intro a b hab
  simp only [shortHash_secondary_eq_mixer, keyWord_update k _ _ (m.length+4) hm,
    ↓reduceIte] at hab
  exact (BitVec.add_right_inj seed).mp
    ((BitVec.xor_right_inj (shortPrepare (shortPack m))).mp (shortFinish_injective hab))
-- CHECKPOINT

theorem short_fingerprint_ordered (seed : Word) (x y : Message)
    (hx : x.length ≤ 8) (hy : y.length ≤ 8) (hlt : x.length < y.length) :
    uniformProb (fun k : OHKey =>
      shortHash k seed x false = shortHash k seed y false ∧
      shortHash k seed x true = shortHash k seed y true) ≤ (1:ℚ≥0)/q^2 := by
  have hxl : x.length < 34 := by omega
  have hyl : y.length < 34 := by omega
  have hx4 : x.length+4 < 34 := by omega
  have hy4 : y.length+4 < 34 := by omega
  let i : Fin 34 := ⟨y.length+4,hy4⟩
  let E := fun k : OHKey => shortHash k seed x false = shortHash k seed y false
  let F := fun k : OHKey => shortHash k seed x true = shortHash k seed y true
  have hE (k : OHKey) (v : Word) : E (Function.update k i v) ↔ E k := by
    simp only [E, shortHash_eq_mixer, keyWord_update k i v x.length hxl,
      keyWord_update k i v y.length hyl, i,
      show x.length ≠ y.length+4 by omega, show y.length ≠ y.length+4 by omega, ↓reduceIte]
  have hs (k : OHKey) : uniformProb (fun v => F (Function.update k i v)) ≤ (1:ℚ≥0)/q := by
    have hfixed (v : Word) : shortHash (Function.update k i v) seed x true =
        shortHash k seed x true := by
      simp only [shortHash_secondary_eq_mixer, keyWord_update k i v (x.length+4) hx4,
        i, show x.length+4 ≠ y.length+4 by omega, ↓reduceIte]
    dsimp only [F]
    simp only [hfixed]
    have hp := probability_bijective_point _ (shortHash_secondary_noise_bijective seed y hy4 k)
      (shortHash k seed x true)
    simpa only [word_card, eq_comm] using hp.le
  have hp := probability_and_update_le E F i ((1:ℚ≥0)/q) hE hs
  have hprim : uniformProb E = (1:ℚ≥0)/q :=
    short_different_length_collision seed x y hx hy (by omega)
  rw [hprim] at hp
  exact hp.trans_eq (by ring)
-- CHECKPOINT

theorem short_fingerprint_iid (seed : Word) (x y : Message)
    (hx : x.length ≤ 8) (hy : y.length ≤ 8) (hxy : x ≠ y) :
    uniformProb (fun k : OHKey =>
      shortHash k seed x false = shortHash k seed y false ∧
      shortHash k seed x true = shortHash k seed y true) ≤ (1:ℚ≥0)/q^2 := by
  by_cases hl : x.length = y.length
  · have he : (fun k : OHKey =>
        shortHash k seed x false = shortHash k seed y false ∧
        shortHash k seed x true = shortHash k seed y true) = (fun _ : OHKey => False) := by
      funext k
      exact propext ⟨fun h => hxy (short_equal_length_injective seed k x y hx hl h.1), False.elim⟩
    rw [he]
    simp only [uniformProb, Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div, zero_le]
  · rcases lt_or_gt_of_ne hl with h | h
    · exact short_fingerprint_ordered seed x y hx hy h
    · simpa only [eq_comm] using short_fingerprint_ordered seed y x hy hx h
-- CHECKPOINT

theorem short_fingerprint_distinct (seed : Word) (x y : Message)
    (hx : x.length ≤ 8) (hy : y.length ≤ 8) (hxy : x ≠ y) :
    uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤
      (1:ℚ≥0)/(q*(q-561):ℕ) := by
  have h := distinct_probability_le
    (fun k : OHKey => shortHash k seed x false = shortHash k seed y false ∧
      shortHash k seed x true = shortHash k seed y true) ((1:ℚ≥0)/q)
    (by simpa only [div_div, pow_two] using short_fingerprint_iid seed x y hx hy hxy)
  let E := fun k : DistinctOHKey => shortHash k.val seed x false = shortHash k.val seed y false ∧
    shortHash k.val seed x true = shortHash k.val seed y true
  have he : (fun k : Key128 => hash128 k seed x = hash128 k seed y) =
      (fun k : Key128 => E k.1) := by
    funext k
    simp only [hash128, hashWith, hx, hy, ↓reduceIte, Prod.mk.injEq, E]
  rw [he, Classic.uniformProb_ignore_right E]
  simpa only [div_div, Nat.cast_mul] using h
-- CHECKPOINT

end ProvenHashes.UMASH
