import ProvenHashes.UMASHClassCard5
import ProvenHashes.UMASHClassCard6
import ProvenHashes.UMASHClassCard7
import ProvenHashes.UMASHClassCard8
import ProvenHashes.UMASHClassCard9
import ProvenHashes.UMASHClassCard10
import ProvenHashes.UMASHClassCard11
import ProvenHashes.UMASHClassCard12
import ProvenHashes.UMASHClassCard13
import ProvenHashes.UMASHClassCard14
import ProvenHashes.UMASHClassCard15
import ProvenHashes.UMASHClassCard16
import ProvenHashes.UMASHClassCard17
import ProvenHashes.UMASHClassCard18
import ProvenHashes.UMASHClassCard19
import ProvenHashes.UMASHClassCard20
import ProvenHashes.UMASHClassCard21
import ProvenHashes.UMASHClassCard22
import ProvenHashes.UMASHClassCard23
import ProvenHashes.UMASHClassCard24
import ProvenHashes.UMASHClassCard25
import ProvenHashes.UMASHClassCard26
import ProvenHashes.UMASHClassCard27
import ProvenHashes.UMASHClassCard28
import ProvenHashes.UMASHClassCard29
import ProvenHashes.UMASHClassCard30
import ProvenHashes.UMASHClassCard31
import ProvenHashes.UMASHClassCard32
import ProvenHashes.UMASHClassCard33
import ProvenHashes.UMASHClassCard34
import ProvenHashes.UMASHClassCard35
import ProvenHashes.UMASHClassCard36
import ProvenHashes.UMASHClassCard37
import ProvenHashes.UMASHClassCard38
import ProvenHashes.UMASHClassCard39
import ProvenHashes.UMASHClassCard40
import ProvenHashes.UMASHClassCard41
import ProvenHashes.UMASHClassCard42
import ProvenHashes.UMASHClassCard43
import ProvenHashes.UMASHClassCard44
import ProvenHashes.UMASHClassCard45
import ProvenHashes.UMASHClassCard46
import ProvenHashes.UMASHClassCard47
import ProvenHashes.UMASHClassCard48
import ProvenHashes.UMASHClassCard49
import ProvenHashes.UMASHClassCard50
import ProvenHashes.UMASHClassCard51
import ProvenHashes.UMASHClassCard52
import ProvenHashes.UMASHClassCard53
import ProvenHashes.UMASHClassCard54
import ProvenHashes.UMASHClassCard55
import ProvenHashes.UMASHClassCard56
import ProvenHashes.UMASHClassCard57
import ProvenHashes.UMASHClassCard58
import ProvenHashes.UMASHClassCard59
import ProvenHashes.UMASHClassCard60
import ProvenHashes.UMASHClassCard61
import ProvenHashes.UMASHClassCard62
import ProvenHashes.UMASHClassCard63

namespace ProvenHashes.UMASH

theorem liftingClasses_card_exact (r : ℕ) (hr : 4 ≤ r) (hr' : r < 64) :
    (liftingClasses r).card = if r = 4 then 36 else 26*r-75 := by
  interval_cases r <;> norm_num only [ite_true, ite_false, liftingClasses_card_4, liftingClasses_card_5, liftingClasses_card_6, liftingClasses_card_7, liftingClasses_card_8, liftingClasses_card_9, liftingClasses_card_10, liftingClasses_card_11, liftingClasses_card_12, liftingClasses_card_13, liftingClasses_card_14, liftingClasses_card_15, liftingClasses_card_16, liftingClasses_card_17, liftingClasses_card_18, liftingClasses_card_19, liftingClasses_card_20, liftingClasses_card_21, liftingClasses_card_22, liftingClasses_card_23, liftingClasses_card_24, liftingClasses_card_25, liftingClasses_card_26, liftingClasses_card_27, liftingClasses_card_28, liftingClasses_card_29, liftingClasses_card_30, liftingClasses_card_31, liftingClasses_card_32, liftingClasses_card_33, liftingClasses_card_34, liftingClasses_card_35, liftingClasses_card_36, liftingClasses_card_37, liftingClasses_card_38, liftingClasses_card_39, liftingClasses_card_40, liftingClasses_card_41, liftingClasses_card_42, liftingClasses_card_43, liftingClasses_card_44, liftingClasses_card_45, liftingClasses_card_46, liftingClasses_card_47, liftingClasses_card_48, liftingClasses_card_49, liftingClasses_card_50, liftingClasses_card_51, liftingClasses_card_52, liftingClasses_card_53, liftingClasses_card_54, liftingClasses_card_55, liftingClasses_card_56, liftingClasses_card_57, liftingClasses_card_58, liftingClasses_card_59, liftingClasses_card_60, liftingClasses_card_61, liftingClasses_card_62, liftingClasses_card_63]
-- CHECKPOINT

theorem liftingClasses_card_le (r : ℕ) (hr : 4 ≤ r) (hr' : r < 64) :
    (liftingClasses r).card ≤ 1563 := by
  rw [liftingClasses_card_exact r hr hr']
  split_ifs <;> omega
-- CHECKPOINT

end ProvenHashes.UMASH
