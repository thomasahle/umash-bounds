import ProvenHashes.UMASHJointOrientation

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

/-- Theorem 7.2, on the literal full joint event. The secondary bound is
conditional on every original chunk key and on the primary event. -/
theorem joint_enh_only_bound : JointENHOnlyBound := by
  intro seed x y hx hy hc hp hne
  have hxlen : 0 < x.chunks.length ∧ x.chunks.length ≤ 16 := by
    rcases hx with ⟨h0,h256,hn⟩
    omega
  have hylen : 0 < y.chunks.length ∧ y.chunks.length ≤ 16 := by
    rcases hy with ⟨h0,h256,hn⟩
    omega
  have hnx := List.ne_nil_of_length_pos hxlen.1
  have hny := List.ne_nil_of_length_pos hylen.1
  have hpre := phDiffCount_zero_prefix x y hc hp
  obtain ⟨r,hr,h1,h2,ho⟩ := chunk_difference_orientation (lastChunk x) (lastChunk y) hne
  let E := fun K : Fin 17 → Chunk => primaryEvent seed x y (keyPairsEquiv.symm K)
  let F := fun K : Fin 17 → Chunk =>
    project (ohSecondary (keyPairsEquiv.symm K) x seed) =
      project (ohSecondary (keyPairsEquiv.symm K) y seed)
  have hind (K : Fin 17 → Chunk) (v : Chunk) : E (Function.update K 16 v) ↔ E K := by
    have hox : oh (keyPairsEquiv.symm (Function.update K 16 v)) x seed =
        oh (keyPairsEquiv.symm K) x seed :=
      congrArg (fun l : List Chunk => l.foldl xorChunk (0,0))
        (mixed_update_later K x seed 16 hxlen.2 v)
    have hoy : oh (keyPairsEquiv.symm (Function.update K 16 v)) y seed =
        oh (keyPairsEquiv.symm K) y seed :=
      congrArg (fun l : List Chunk => l.foldl xorChunk (0,0))
        (mixed_update_later K y seed 16 hylen.2 v)
    dsimp only [E, primaryEvent]
    rw [hox, hoy]
  have hs (K : Fin 17 → Chunk) (hE : E K) :
      uniformProb (fun v => F (Function.update K 16 v)) ≤ (852:ℚ≥0)/q := by
    let k := keyPairsEquiv.symm K
    have hcheck := checksum_ne_of_last k x y hnx hny hpre hne
    have hcx := congrArg Prod.fst (checksum_xor_of_prefix k x y hnx hny hpre)
    have hcy := congrArg Prod.snd (checksum_xor_of_prefix k x y hnx hny hpre)
    change (checksum k x).1 ^^^ (checksum k y).1 = (lastChunk x).1 ^^^ (lastChunk y).1 at hcx
    change (checksum k x).2 ^^^ (checksum k y).2 = (lastChunk x).2 ^^^ (lastChunk y).2 at hcy
    have hd1 : 2^r ∣ ((checksum k x).1 ^^^ (checksum k y).1).toNat := by rw [hcx]; exact h1
    have hd2 : 2^r ∣ ((checksum k x).2 ^^^ (checksum k y).2).toNat := by rw [hcy]; exact h2
    have hor : ((checksum k x).1 ≠ (checksum k y).1 ∧
        r = padicValNat 2 ((checksum k x).1 ^^^ (checksum k y).1).toNat) ∨
        ((checksum k x).2 ≠ (checksum k y).2 ∧
        r = padicValNat 2 ((checksum k x).2 ^^^ (checksum k y).2).toNat) := by
      rcases ho with ho | ho
      · left
        refine ⟨?_, by simpa only [hcx] using ho.2⟩
        intro he
        have hz : (lastChunk x).1 ^^^ (lastChunk y).1 = 0 := by rw [← hcx, he, BitVec.xor_self]; rfl
        exact ho.1 (BitVec.xor_eq_zero_iff.mp hz)
      · right
        refine ⟨?_, by simpa only [hcy] using ho.2⟩
        intro he
        have hz : (lastChunk x).2 ^^^ (lastChunk y).2 = 0 := by rw [← hcy, he, BitVec.xor_self]; rfl
        exact ho.1 (BitVec.xor_eq_zero_iff.mp hz)
    dsimp only [F]
    simp only [secondary_twist_slice K x seed hxlen.2, secondary_twist_slice K y seed hylen.2]
    by_cases hr4 : r < 4
    · exact masked_ph_small_valuation_probability (checksum k x) (checksum k y)
        (secondaryBody k x seed) (secondaryBody k y seed) r hr4 hd1 hd2
        (secondaryBody_low_prefix k seed x y hnx hny hpre r hr.le h1 h2) hor
    · have h16 : 16 ∣ 2^r := pow_dvd_pow 2 (by omega : 4 ≤ r)
      exact masked_ph_high_valuation_probability (checksum k x) (checksum k y)
        (secondaryBody k x seed) (secondaryBody k y seed) hcheck (h16.trans hd1) (h16.trans hd2)
        (primary_event_implies_body_low_eq k seed x y hnx hny hpre
          (h16.trans h1) (h16.trans h2) hE)
  have hprod := probability_and_update_event_le E F 16 ((852:ℚ≥0)/q) hind hs
  have hequiv : uniformProb E = uniformProb (primaryEvent seed x y) :=
    uniformProb_equiv keyPairsEquiv.symm _
  have hjoint : uniformProb (fun K => E K ∧ F K) = uniformProb (jointEvent seed x y) :=
    uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)
  rw [hequiv, hjoint] at hprod
  calc
    _ ≤ uniformProb (primaryEvent seed x y)*((852:ℚ≥0)/q) := hprod
    _ ≤ ((5542:ℚ≥0)/q)*((852:ℚ≥0)/q) :=
      mul_le_mul_of_nonneg_right (primary_enh_only_bound seed x y hx hy hc hp hne) (by positivity)
    _ = _ := by ring
-- CHECKPOINT

/-- A second closure, now through the exact requested joint numerator. -/
theorem open_enh_only_sharp : OpenENHOnly := openENHOnly_of_joint joint_enh_only_bound
-- CHECKPOINT

end ProvenHashes.UMASH
