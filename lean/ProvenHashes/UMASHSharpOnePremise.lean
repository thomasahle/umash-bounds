import ProvenHashes.UMASHTagSharp
import ProvenHashes.UMASHBlock3125

namespace ProvenHashes.UMASH

/-- The tag-only premise has been discharged. Only PROOF3 Theorem 4.1
remains before the closed 3125 block and message bounds. -/
theorem primary_block3125_of_ph (hph : PrimaryPHBound1123) : PrimaryBlockBound3125 :=
  primary_block3125_of_ph_and_tag hph primary_tag_only_sharp
-- CHECKPOINT

theorem certified64_3125_of_ph (hph : PrimaryPHBound1123) : CertifiedAllPairs64_3125 :=
  certified64_3125_of_ph_and_tag hph primary_tag_only_sharp
-- CHECKPOINT

theorem certified128_3125_of_ph (hph : PrimaryPHBound1123) : CertifiedAllPairs128_3125 :=
  certified128_3125_of_ph_and_tag hph primary_tag_only_sharp
-- CHECKPOINT

theorem correctedLinear64_423_of_ph (hph : PrimaryPHBound1123) : CorrectedLinear64_423 :=
  correctedLinear64_423_of_certified (certified64_3125_of_ph hph)
-- CHECKPOINT

theorem correctedLinear128_423_of_ph (hph : PrimaryPHBound1123) : CorrectedLinear128_423 :=
  correctedLinear128_423_of_64 (correctedLinear64_423_of_ph hph)
-- CHECKPOINT

end ProvenHashes.UMASH
