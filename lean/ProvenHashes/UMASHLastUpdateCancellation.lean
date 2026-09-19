import ProvenHashes.UMASHAccumulator

/-! Literal last-update cancellation for the argument from the GPT-6 Pro handoff of 2026-09-19, Section 7. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

theorem polyStep_cancel_acc (f acc : ℕ) (x y : Chunk) :
    polyStep f acc x = polyStep f acc y ↔ polyStep f 0 x = polyStep f 0 y := by
  change Nat.ModEq (q-8) ((f*f%p)*(acc+x.1.toNat)+f*x.2.toNat)
    ((f*f%p)*(acc+y.1.toNat)+f*y.2.toNat) ↔
      Nat.ModEq (q-8) ((f*f%p)*(0+x.1.toNat)+f*x.2.toNat)
        ((f*f%p)*(0+y.1.toNat)+f*y.2.toNat)
  simp only [zero_add,Nat.mul_add,Nat.add_assoc]
  exact ⟨Nat.ModEq.add_left_cancel' _,fun h => h.add_left _⟩
-- CHECKPOINT

theorem finalized_polyStep_eq_iff (f acc : ℕ) (x y : Chunk) :
    finalize (BitVec.ofNat 64 (polyStep f acc x)) =
      finalize (BitVec.ofNat 64 (polyStep f acc y)) ↔ polyStep f acc x = polyStep f acc y := by
  constructor
  · intro he
    have hraw := congrArg BitVec.toNat (finalize_injective he)
    have hlt (z : Chunk) : polyStep f acc z < 2^64 :=
      (Nat.mod_lt _ (by norm_num [q] : 0 < q-8)).trans_le (Nat.sub_le q 8)
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (hlt x),Nat.mod_eq_of_lt (hlt y)] using hraw
  · intro he
    rw [he]
-- CHECKPOINT

/-- The common accumulator may depend on every key and on f: cancellation
is pointwise, so no independence from that accumulator is needed. -/
theorem finalized_polyReduce_last_cancel (f acc : ℕ) (xs : List Chunk) (x y : Chunk) :
    finalize (BitVec.ofNat 64 (polyReduce f (xs++[x]) acc)) =
      finalize (BitVec.ofNat 64 (polyReduce f (xs++[y]) acc)) ↔
        polyStep f 0 x = polyStep f 0 y := by
  simp only [polyReduce,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [finalized_polyStep_eq_iff,polyStep_cancel_acc]
-- CHECKPOINT

end ProvenHashes.UMASH
