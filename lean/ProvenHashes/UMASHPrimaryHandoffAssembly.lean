import ProvenHashes.UMASHPrimaryHandoffObligations
import ProvenHashes.UMASHPrimaryMessageCases
import ProvenHashes.UMASHPrimaryRates

/-! Complete primary endpoint assembly from two explicitly open block estimates,
using the argument from the GPT-6 Pro handoff of 2026-09-19, Section 7.
No conditional theorem is named `published64`. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] uniformProb wordFintype rootRate

theorem primary_probability_of_iid (seed : Word) (x y : Message) (C : ℚ≥0)
    (h : uniformProb (fun k : OHKey × PolyKey =>
      hashWith k.1 k.2.val.val seed x = hashWith k.1 k.2.val.val seed y) ≤ C) :
    uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
      C/(((q-561:ℕ):ℚ≥0)/q) := distinct_product_probability_le _ C h
-- CHECKPOINT

theorem primary_iid_of_identity (L : ℕ) (seed : Word) (x y : Message) (B : ℚ≥0)
    (hx : x.length ≤ 8*L) (hy : y.length ≤ 8*L)
    (hb : uniformProb (fun k : OHKey =>
      comparisonPolynomial k seed x = comparisonPolynomial k seed y) ≤ B) :
    uniformProb (fun k : OHKey × PolyKey =>
      hashWith k.1 k.2.val.val seed x = hashWith k.1 k.2.val.val seed y) ≤ B+rootRate L := by
  exact probability_mixture_add _ _ _ _ hb
    (fun k hk => comparison_slice_bound L k seed x y hx hy hk)
-- CHECKPOINT

theorem primary_earlier_full_of_handoff (hfull : PrimaryFullBlockBound256)
    (L : ℕ) (seed : Word) (x y : Message) (bx byy : Block)
    (hL : 1 ≤ L) (hx : x.length ≤ 8*L) (hy : y.length ≤ 8*L)
    (hxl : 8 < x.length) (hyl : 8 < y.length)
    (hvx : bx.Valid) (hvy : byy.Valid) (hsx : bx.byteSize = 256) (hsy : byy.byteSize = 256)
    (hne : bx.chunks ≠ byy.chunks)
    (hw : ∀ k : OHKey, comparisonPolynomial k seed x = comparisonPolynomial k seed y →
      primaryEvent seed bx byy k) :
    uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
      ((L+511)/512:ℕ)/(2:ℚ≥0)^55 := by
  have hid := (probability_mono hw).trans (hfull seed bx byy hvx hvy hsx hsy hne)
  have hiid := probability_mixture_add
    (fun k : OHKey × PolyKey => hashWith k.1 k.2.val.val seed x = hashWith k.1 k.2.val.val seed y)
    (fun k : OHKey => comparisonPolynomial k seed x = comparisonPolynomial k seed y)
    (((2*((L+31)/32)-1:ℕ):ℚ≥0)/(p-2:ℕ)) ((256:ℚ≥0)/q) hid
    (fun k hk => long_comparison_slice_excluded_zero L k seed x y hx hy hxl hyl hk)
  exact (primary_probability_of_iid seed x y _ hiid).trans (primary_earlier_rate_le_published L hL)
-- CHECKPOINT

theorem primary_last_of_handoff (hlast : PrimaryLastUpdateBound503)
    (L : ℕ) (seed : Word) (x y : Message) (hL : 1 ≤ L)
    (hx : 8 < x.length) (hy : 8 < y.length) (bs : List Block) (bx byy : Block)
    (hvx : bx.Valid) (hvy : byy.Valid)
    (ht : bx.chunks ≠ byy.chunks ∨ blockTag seed bx ≠ blockTag seed byy)
    (hex : encode x = bs++[bx]) (hey : encode y = bs++[byy]) :
    uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
      ((L+511)/512:ℕ)/(2:ℚ≥0)^55 := by
  have hiid : uniformProb (fun k : OHKey × PolyKey =>
      hashWith k.1 k.2.val.val seed x = hashWith k.1 k.2.val.val seed y) ≤ (503:ℚ≥0)/q := by
    apply (probability_mono ?_).trans (hlast seed bx byy hvx hvy ht).le
    intro k hk
    exact (hashWith_common_prefix_last_iff k.1 k.2.val.val seed x y hx hy bs bx byy hex hey).mp hk
  exact (primary_probability_of_iid seed x y _ hiid).trans (primary_last_rate_le_published L hL)
-- CHECKPOINT

theorem primary_other_counts_published (L : ℕ) (seed : Word) (x y : Message)
    (hL : 1 ≤ L) (hx : x.length ≤ 8*L) (hy : y.length ≤ 8*L)
    (hxl : 8 < x.length) (hyl : 8 < y.length)
    (hc : (encode x).length ≠ (encode y).length) :
    uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
      ((L+511)/512:ℕ)/(2:ℚ≥0)^55 := by
  have hiid := primary_iid_of_identity L seed x y ((82:ℚ≥0)/q) hx hy
    (corrected_different_block_counts_bound seed x y hxl hyl hc).le
  exact (primary_probability_of_iid seed x y _ hiid).trans (primary_other_rate_le_published L hL)
-- CHECKPOINT

theorem primary_short_long_published (L : ℕ) (seed : Word) (x y : Message)
    (hL : 1 ≤ L) (hx : x.length ≤ 8*L) (hy : y.length ≤ 8*L)
    (hxs : x.length ≤ 8) (hyl : 8 < y.length) :
    uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
      ((L+511)/512:ℕ)/(2:ℚ≥0)^55 := by
  have hid := (short_long_identity_probability seed x y hxs hyl).trans
    (show (9:ℚ≥0)/q ≤ (82:ℚ≥0)/q by apply NNRat.coe_le_coe.mp; norm_num [q])
  have hiid := primary_iid_of_identity L seed x y ((82:ℚ≥0)/q) hx hy hid
  exact (primary_probability_of_iid seed x y _ hiid).trans (primary_other_rate_le_published L hL)
-- CHECKPOINT

theorem published64_of_primary_handoff : PrimaryHandoffAssembly := by
  intro hfull hlast L seed x y hL hx hy hne
  by_cases hxl : 8 < x.length
  · by_cases hyl : 8 < y.length
    · by_cases hc : (encode x).length = (encode y).length
      · rcases long_primary_message_cases seed x y hxl hyl hne hc with
          ⟨bx,byy,hvx,hvy,hsx,hsy,hb,hw⟩ | ⟨bs,bx,byy,hvx,hvy,ht,hex,hey⟩
        · exact primary_earlier_full_of_handoff hfull L seed x y bx byy hL hx hy hxl hyl hvx hvy hsx hsy hb hw
        · exact primary_last_of_handoff hlast L seed x y hL hxl hyl bs bx byy hvx hvy ht hex hey
      · exact primary_other_counts_published L seed x y hL hx hy hxl hyl hc
    · simpa only [eq_comm] using primary_short_long_published L seed y x hL hy hx (by omega) hxl
  · by_cases hyl : 8 < y.length
    · exact primary_short_long_published L seed x y hL hx hy (by omega) hyl
    · exact (short_one_word_bound seed x y (by omega) (by omega) hne).trans
        ((show (1:ℚ≥0)/(q-561:ℕ) ≤ ((503:ℚ≥0)/q)/(((q-561:ℕ):ℚ≥0)/q) by
          apply NNRat.coe_le_coe.mp; norm_num [q]).trans (primary_last_rate_le_published L hL))
-- CHECKPOINT

end ProvenHashes.UMASH
