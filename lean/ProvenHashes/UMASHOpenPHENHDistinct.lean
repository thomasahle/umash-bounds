import ProvenHashes.UMASHOpenPHENH

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

/-- The original strict 87-bit threshold survives conditioning all 34 OH
words to be distinct. The requested sharper 90-bit transfer remains separate. -/
theorem phenh_open_distinct (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y)
    (hsum : dataChecksum x = dataChecksum y)
    (hp : phDiffCount x y = 1) (he : enhChanges x y = 2)
    (hr : 1 ≤ enhValuation x y) (hr' : enhValuation x y ≤ 63) :
    uniformProb (fun k : DistinctOHKey => jointEvent seed x y k.val) < (1:ℚ≥0)/2^87 := by
  have hh := distinct_probability_le (jointEvent seed x y) ((2058363321984:ℚ≥0)/q)
    (by simpa only [div_div, pow_two] using
      joint_phenh_open_bound seed x y hx hy hc hsum hp he hr hr')
  exact hh.trans_lt (by norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
