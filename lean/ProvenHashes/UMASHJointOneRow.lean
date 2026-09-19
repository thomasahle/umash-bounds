import ProvenHashes.UMASHJointBlock
import ProvenHashes.UMASHTwoPHBound

namespace ProvenHashes.UMASH

/-- Every joint block branch except the one-word PH+ENH row is closed. -/
theorem joint_block_bound_of_one_row (hW : PHOneWordENHBound) :
    JointBlockBound1416246956032 := joint_block_bound_of_two_rows subcase_b_bound hW
-- CHECKPOINT

end ProvenHashes.UMASH
