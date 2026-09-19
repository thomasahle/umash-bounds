import ProvenHashes.UMASHMaskCensus3125

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] maskSet

def maskPrefixCount (s c : ℕ) : ℕ :=
  (maskSet.filter (fun d => d % 2^s = c)).card

def smallMaskPrefixTable (s : ℕ) : List ℕ :=
  if s = 1 then [248,604] else if s = 2 then [64,242,184,362]
  else [2,62,62,122,62,180,122,240]

theorem maskPrefixCount_one (c : Fin 2) :
    maskPrefixCount 1 c.val = (smallMaskPrefixTable 1)[c.val]! := by
  unfold maskPrefixCount
  rw [maskSet_eq_fastCertificate]
  revert c
  decide +kernel
-- CHECKPOINT

theorem maskPrefixCount_two (c : Fin 4) :
    maskPrefixCount 2 c.val = (smallMaskPrefixTable 2)[c.val]! := by
  unfold maskPrefixCount
  rw [maskSet_eq_fastCertificate]
  revert c
  decide +kernel
-- CHECKPOINT

theorem maskPrefixCount_three (c : Fin 8) :
    maskPrefixCount 3 c.val = (smallMaskPrefixTable 3)[c.val]! := by
  unfold maskPrefixCount
  rw [maskSet_eq_fastCertificate]
  revert c
  decide +kernel
-- CHECKPOINT

theorem maskPrefixCount_small (s c : ℕ) (hs : 1 ≤ s) (hs3 : s ≤ 3) (hc : c < 2^s) :
    maskPrefixCount s c = (smallMaskPrefixTable s)[c]! := by
  interval_cases s
  · exact maskPrefixCount_one ⟨c,hc⟩
  · exact maskPrefixCount_two ⟨c,hc⟩
  · exact maskPrefixCount_three ⟨c,hc⟩
-- CHECKPOINT

def smallPHConvolution (s δ ε : ℕ) : ℕ :=
  ((List.range (2^s)).map (fun a => ((List.range (2^s)).map (fun b =>
    maskPrefixCount s ((a*b%2^s) ^^^ ((a+δ)*(b+ε)%2^s)))).sum)).sum

def smallPHConvolutionTable (s δ ε : ℕ) : ℕ :=
  ((List.range (2^s)).map (fun a => ((List.range (2^s)).map (fun b =>
    (smallMaskPrefixTable s)[(a*b%2^s) ^^^ ((a+δ)*(b+ε)%2^s)]!)).sum)).sum

theorem smallPHConvolution_eq_table (s δ ε : ℕ) (hs : 1 ≤ s) (hs3 : s ≤ 3) :
    smallPHConvolution s δ ε = smallPHConvolutionTable s δ ε := by
  unfold smallPHConvolution smallPHConvolutionTable
  congr 1
  apply List.map_congr_left
  intro a _
  congr 1
  apply List.map_congr_left
  intro b _
  exact maskPrefixCount_small s _ hs hs3
    (Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity)))
-- CHECKPOINT

/-- The four, sixteen and sixty-four increment cases of PROOF3 (8). -/
theorem smallPHConvolutionTable_certificate :
    (∀ δ ε : Fin 2, smallPHConvolutionTable 1 δ.val ε.val ≤ 1704) ∧
    (∀ δ ε : Fin 4, smallPHConvolutionTable 2 δ.val ε.val ≤ 3408) ∧
    (∀ δ ε : Fin 8, smallPHConvolutionTable 3 δ.val ε.val ≤ 6816) := by
  decide +kernel
-- CHECKPOINT

theorem smallPHConvolution_le (s δ ε : ℕ) (hs : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : δ < 2^s) (hε : ε < 2^s) : smallPHConvolution s δ ε ≤ 852*2^s := by
  rw [smallPHConvolution_eq_table s δ ε hs hs3]
  interval_cases s
  · exact smallPHConvolutionTable_certificate.1 ⟨δ,hδ⟩ ⟨ε,hε⟩
  · exact smallPHConvolutionTable_certificate.2.1 ⟨δ,hδ⟩ ⟨ε,hε⟩
  · exact smallPHConvolutionTable_certificate.2.2 ⟨δ,hδ⟩ ⟨ε,hε⟩
-- CHECKPOINT

/-- The valuation ledger in PROOF3 Theorem 4.1, before probabilistic assembly. -/
theorem primaryPHConvolution_arithmetic (s : ℕ) (hs : s < 64) :
    852 ≤ 1123 ∧ 2+184*4+62*5+s+12 ≤ 1123 ∧
    4+62*8+s+12 ≤ 575 ∧ 8+16 ≤ 1123 := by omega
-- CHECKPOINT

end ProvenHashes.UMASH
