import ProvenHashes.UMASHGroupedCount
import ProvenHashes.UMASHFunctionClassCertificate
import ProvenHashes.UMASHSharpObligations
import ProvenHashes.UMASHBlockENH

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem enh_high_valuation_probability3125 (r δ ε tag tag' ML MH : ℕ)
    (h4 : 4 ≤ r) (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hδq : δ < q) (hεq : ε < q) (hML : ML < q) (hMH : MH < q) :
    uniformProb (enhProjectedEvent δ ε tag tag' ML MH) ≤ (3125:ℚ≥0)/q := by
  have hd16 : 16 ∣ δ := (pow_dvd_pow 2 h4).trans hδ
  have he16 : 16 ∣ ε := (pow_dvd_pow 2 h4).trans hε
  have hc : 2*(liftingClasses r).card-1 ≤ 3125 := by
    have hh := liftingClasses_card_le r h4 hr
    omega
  exact (probability_mono (enh_projected_implies_low_equal δ ε tag tag' ML MH
    hd16 he16 hML)).trans
    ((enh_grouped_class_probability r δ ε tag tag' MH h4 hr hδ hε hodd hδq hεq hMH).trans
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity)))
-- CHECKPOINT

/-- All valuations, arbitrary tags, and both arbitrary common XOR masks. -/
theorem enh_projected_probability3125 (r δ ε tag tag' ML MH : ℕ)
    (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hδq : δ < q) (hεq : ε < q) (hML : ML < q) (hMH : MH < q) :
    uniformProb (enhProjectedEvent δ ε tag tag' ML MH) ≤ (3125:ℚ≥0)/q := by
  by_cases h4 : 4 ≤ r
  · exact enh_high_valuation_probability3125 r δ ε tag tag' ML MH
      h4 hr hδ hε hodd hδq hεq hML hMH
  · have hc : 2^r*patternWeight r ≤ 3125 := by
      have hr4 : r < 4 := by omega
      interval_cases r <;> norm_num [patternWeight_table.1, patternWeight_table.2.1,
        patternWeight_table.2.2.1, patternWeight_table.2.2.2.1]
    exact (probability_mono (fun ab (he : enhProjectedEvent δ ε tag tag' ML MH ab) => he.1)).trans
      ((low_projection_bound r δ ε ML hr hδ hε hodd hML).trans
        (div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity)))
-- CHECKPOINT

/-- The operand bound needs only distinct input data, with no valuation premise. -/
theorem enh_projected_probability_any3125 (δ ε tag tag' ML MH : ℕ)
    (hδq : δ < q) (hεq : ε < q) (hne : δ ≠ 0 ∨ ε ≠ 0)
    (hML : ML < q) (hMH : MH < q) :
    uniformProb (enhProjectedEvent δ ε tag tag' ML MH) ≤ (3125:ℚ≥0)/q := by
  obtain ⟨r, hr, hδ, hε, ho⟩ := increment_orientation δ ε hδq hεq hne
  rcases ho with ho | ho
  · exact enh_projected_probability3125 r δ ε tag tag' ML MH hr hδ hε ho hδq hεq hML hMH
  · calc
      _ = uniformProb (fun ab : Chunk =>
          enhProjectedEvent ε δ tag tag' ML MH ((Equiv.prodComm Word Word) ab)) :=
        congrArg uniformProb (funext fun ab => propext
          (enhProjectedEvent_swap δ ε tag tag' ML MH ab))
      _ = uniformProb (enhProjectedEvent ε δ tag tag' ML MH) :=
        uniformProb_equiv (Equiv.prodComm Word Word) _
      _ ≤ _ := enh_projected_probability3125 r ε δ tag tag' ML MH
        hr hε hδ ho hεq hδq hML hMH
-- CHECKPOINT

/-- The literal ENH bound for any two distinct data chunks under uniform keys. -/
theorem masked_enh_probability3125 (data data' M : Chunk) (tag tag' : Word)
    (hne : data ≠ data') :
    uniformProb (fun key : Chunk => project (xorChunk M (enh key data tag)) =
      project (xorChunk M (enh key data' tag'))) ≤ (3125:ℚ≥0)/q := by
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
    _ ≤ _ := enh_projected_probability_any3125 δ ε tag.toNat tag'.toNat M.1.toNat M.2.toNat
      (data'.1-data.1).isLt (data'.2-data.2).isLt hd M.1.isLt M.2.isLt
-- CHECKPOINT

/-- PROOF3 Theorem 5.4 for the actual block hash and all 34 IID OH key words. -/
theorem primary_enh_only_bound3125 : PrimaryENHOnlyBound3125 := by
  intro seed x y hx hy hc hp hne
  have hxlen : 0 < x.chunks.length ∧ x.chunks.length ≤ 16 := by
    rcases hx with ⟨h0,h256,hn⟩
    omega
  have hylen : 0 < y.chunks.length := by
    change x.chunks.length = y.chunks.length at hc
    omega
  have hnx : x.chunks ≠ [] := List.ne_nil_of_length_pos hxlen.1
  have hny : y.chunks ≠ [] := List.ne_nil_of_length_pos hylen
  have hpre := phDiffCount_zero_prefix x y hc hp
  let xs := x.chunks.dropLast
  have hxs : x.chunks = xs ++ [lastChunk x] := block_chunks_split x hnx
  have hys : y.chunks = xs ++ [lastChunk y] := by
    dsimp only [xs]
    rw [hpre]
    exact block_chunks_split y hny
  have hn : xs.length < 17 := by
    dsimp only [xs]
    rw [List.length_dropLast]
    omega
  let j : Fin 17 := ⟨xs.length,hn⟩
  rw [← uniformProb_equiv keyPairsEquiv.symm (primaryEvent seed x y)]
  apply probability_le_of_update _ j
  intro K
  have hox (v : Chunk) : oh (keyPairsEquiv.symm (Function.update K j v)) x seed =
      xorChunk (phPrefix (keyPairsEquiv.symm K) xs) (enh v (lastChunk x) (blockTag seed x)) := by
    rw [oh_append_last _ x seed xs (lastChunk x) hxs,
      phPrefix_update_later K xs j le_rfl v, keyPair_of_pairs _ xs.length hn]
    simp [j]
  have hoy (v : Chunk) : oh (keyPairsEquiv.symm (Function.update K j v)) y seed =
      xorChunk (phPrefix (keyPairsEquiv.symm K) xs) (enh v (lastChunk y) (blockTag seed y)) := by
    rw [oh_append_last _ y seed xs (lastChunk y) hys,
      phPrefix_update_later K xs j le_rfl v, keyPair_of_pairs _ xs.length hn]
    simp [j]
  simp only [primaryEvent, hox, hoy]
  exact masked_enh_probability3125 (lastChunk x) (lastChunk y)
    (phPrefix (keyPairsEquiv.symm K) xs) (blockTag seed x) (blockTag seed y) hne
-- CHECKPOINT

end ProvenHashes.UMASH
