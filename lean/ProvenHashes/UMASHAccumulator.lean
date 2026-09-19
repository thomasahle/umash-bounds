import ProvenHashes.UMASHPolynomial

namespace ProvenHashes.UMASH

/-- Exact equality in the implemented accumulator, retaining modulus q-8.
The square of the multiplier is reduced modulo p exactly as in polyStep. -/
theorem polyStep_eq_iff_high_divides (f acc : ℕ) (x y : Chunk) (hl : x.1 = y.1) :
    polyStep f acc x = polyStep f acc y ↔
      ((q-8:ℕ):ℤ) ∣ (f:ℤ)*((y.2.toNat:ℤ)-x.2.toNat) := by
  change Nat.ModEq (q-8)
    ((f*f%p)*(acc+x.1.toNat)+f*x.2.toNat)
    ((f*f%p)*(acc+y.1.toNat)+f*y.2.toNat) ↔ _
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
  congr 1
  push_cast
  rw [hl]
  ring
-- CHECKPOINT

/-- PROOF4 Lemma 7.1, as an equivalence for the literal final update.
Neither the range of the multiplier nor a bound on j is needed here. -/
theorem polyStep_high_multiple_iff (f acc : ℕ) (x y : Chunk) (j : ℤ)
    (hl : x.1 = y.1) (hj : (y.2.toNat:ℤ)-x.2.toNat = j*(p:ℤ)) :
    polyStep f acc x = polyStep f acc y ↔ (8:ℤ) ∣ (f:ℤ)*j := by
  rw [polyStep_eq_iff_high_divides f acc x y hl, hj]
  have hq : ((q-8:ℕ):ℤ) = 8*(p:ℤ) := by norm_num [q, p]
  rw [hq, ← mul_assoc]
  exact mul_dvd_mul_iff_right (by norm_num [p] : (p:ℤ) ≠ 0)
-- CHECKPOINT

/-- The reference finalizer and word conversion do not erase the modulo-8p
condition: every literal accumulator result is strictly below q. -/
theorem finalized_polyStep_high_multiple_iff (f acc : ℕ) (x y : Chunk) (j : ℤ)
    (hl : x.1 = y.1) (hj : (y.2.toNat:ℤ)-x.2.toNat = j*(p:ℤ)) :
    finalize (BitVec.ofNat 64 (polyStep f acc x)) =
      finalize (BitVec.ofNat 64 (polyStep f acc y)) ↔ (8:ℤ) ∣ (f:ℤ)*j := by
  rw [← polyStep_high_multiple_iff f acc x y j hl hj]
  constructor
  · intro he
    have hraw := congrArg BitVec.toNat (finalize_injective he)
    have hlt (z : Chunk) : polyStep f acc z < 2^64 := by
      exact (Nat.mod_lt _ (by norm_num [q] : 0 < q-8)).trans_le (Nat.sub_le q 8)
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hlt x),
      Nat.mod_eq_of_lt (hlt y)] using hraw
  · intro he
    rw [he]
-- CHECKPOINT

/-- Identical literal prefixes reduce to Lemma 7.1 with their common actual
accumulator. No equality of field representatives is substituted for it. -/
theorem finalized_polyReduce_last_high_multiple_iff (f acc : ℕ) (xs : List Chunk)
    (x y : Chunk) (j : ℤ) (hl : x.1 = y.1)
    (hj : (y.2.toNat:ℤ)-x.2.toNat = j*(p:ℤ)) :
    finalize (BitVec.ofNat 64 (polyReduce f (xs++[x]) acc)) =
      finalize (BitVec.ofNat 64 (polyReduce f (xs++[y]) acc)) ↔ (8:ℤ) ∣ (f:ℤ)*j := by
  simpa only [polyReduce, List.foldl_append, List.foldl_cons, List.foldl_nil] using
    finalized_polyStep_high_multiple_iff f (polyReduce f xs acc) x y j hl hj
-- CHECKPOINT

end ProvenHashes.UMASH
