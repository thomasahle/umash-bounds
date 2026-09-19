import ProvenHashes.UMASHLowMinimal
import ProvenHashes.UMASHModularProduct

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb

theorem lowENHXor_mod_width (n s δ ε A B : ℕ) (hs : s ≤ n) :
    lowENHXor n δ ε A B % 2^s = lowENHXor s δ ε A B := by
  simp only [lowENHXor, Nat.xor_mod_two_pow,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hs)]
-- CHECKPOINT

theorem lowENHXor_mod_operands (n δ ε A B : ℕ) :
    lowENHXor n δ ε (A%2^n) (B%2^n) = lowENHXor n δ ε A B := by
  simp [lowENHXor, Nat.add_mod, Nat.mul_mod]
-- CHECKPOINT

theorem lowENHXor_mod_increments (n δ ε A B : ℕ) :
    lowENHXor n (δ%2^n) (ε%2^n) A B = lowENHXor n δ ε A B := by
  simp [lowENHXor, Nat.add_mod, Nat.mul_mod]
-- CHECKPOINT

/-- Truncation preserves the exact low-XOR law of independent uniform
operands. No nonzero-increment hypothesis is required. -/
theorem lowENHXor_uniform_truncate (n s δ ε e : ℕ) (hs : s ≤ n) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      lowENHXor s δ ε ab.1.val ab.2.val = e) =
    uniformProb (fun ab : Fin (2^s) × Fin (2^s) =>
      lowENHXor s δ ε ab.1.val ab.2.val = e) := by
  let R := 2^(n-s)
  have hR : 0 < R := by dsimp [R]; positivity
  have hQ : 0 < 2^s := by positivity
  have hpow : R*2^s = 2^n := by
    dsimp [R]
    rw [← pow_add, Nat.sub_add_cancel hs]
  let equiv := Equiv.prodCongr (finCongr hpow) (finCongr hpow)
  rw [← uniformProb_equiv equiv]
  change uniformProb (fun ab : Fin (R*2^s) × Fin (R*2^s) =>
    lowENHXor s δ ε ab.1.val ab.2.val = e) = _
  have h := uniform_pair_mod_lifts R (2^s) hR hQ
    (fun ab : ZMod (2^s) × ZMod (2^s) => lowENHXor s δ ε ab.1.val ab.2.val = e)
  simpa only [ZMod.val_natCast, lowENHXor_mod_operands] using h
-- CHECKPOINT

/-- The bottom s bits of the full product-XOR difference have exactly
the width-s distribution used in PROOF3's convolution. -/
theorem lowENHXor_prefix_probability (n s δ ε e : ℕ) (hs : s ≤ n) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      lowENHXor n δ ε ab.1.val ab.2.val % 2^s = e) =
    uniformProb (fun ab : Fin (2^s) × Fin (2^s) =>
      lowENHXor s (δ%2^s) (ε%2^s) ab.1.val ab.2.val = e) := by
  simp only [lowENHXor_mod_width n s δ ε _ _ hs, lowENHXor_mod_increments]
  exact lowENHXor_uniform_truncate n s δ ε e hs
-- CHECKPOINT

end ProvenHashes.UMASH
