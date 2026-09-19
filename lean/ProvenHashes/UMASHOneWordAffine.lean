import ProvenHashes.UMASHHighProduct
import ProvenHashes.UMASHLowXorUniform

/-! The triangular affine-XOR step in the one-word ENH atom argument from
the GPT-6 Pro handoff of 2026-09-19, earlier ENH notes §4. Fixed tags are
retained as independent additive offsets. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

def affineXorNat (n a b c d z : ℕ) : ℕ :=
  ((a*z+c)%2^n) ^^^ ((b*z+d)%2^n)

theorem affine_xor_congruence (n a b c d z e : ℕ)
    (he : affineXorNat n a b c d z = e) :
    Int.ModEq ((2:ℤ)^n)
      (((b:ℤ)-a)*z+((d:ℤ)-c)+2*((a*z+c)&&&e:ℕ)) (e:ℤ) := by
  let U := (a*z+c)%2^n
  let V := (b*z+d)%2^n
  have he' : U ^^^ V = e := he
  have heLt : e < 2^n := by
    rw [← he']
    exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
  have hd := xor_signed_difference U V
  rw [he'] at hd
  have hU : Int.ModEq ((2:ℤ)^n) ((a*z+c:ℕ):ℤ) (U:ℤ) := by
    exact_mod_cast (Int.natCast_modEq_iff.mpr (Nat.mod_mod (a*z+c) (2^n)).symm)
  have hV : Int.ModEq ((2:ℤ)^n) ((b*z+d:ℕ):ℤ) (V:ℤ) := by
    exact_mod_cast (Int.natCast_modEq_iff.mpr (Nat.mod_mod (b*z+d) (2^n)).symm)
  have hm : U &&& e = (a*z+c)&&&e := and_mod_word n (a*z+c) e heLt
  have hh := (hV.sub hU).add_right (2*(U &&& e:ℕ):ℤ)
  have hd' : (V:ℤ)-U+2*(U &&& e:ℕ) = e := by omega
  rw [hd',hm] at hh
  convert hh using 1 <;> push_cast <;> ring
-- CHECKPOINT

theorem affine_mask_prefix (a c e x y j : ℕ) (h : x%2^j = y%2^j) :
    ((a*x+c)&&&e)%2^j = ((a*y+c)&&&e)%2^j := by
  rw [Nat.and_mod_two_pow,Nat.and_mod_two_pow]
  congr 1
  exact (Nat.ModEq.mul_left a h).add_right c
-- CHECKPOINT

theorem affine_xor_odd_injective (n a b c d : ℕ) (hab : ((b:ℤ)-a)%2 = 1) :
    Function.Injective (fun z : Fin (2^n) => affineXorNat n a b c d z.val) := by
  intro x y he
  have hx := affine_xor_congruence n a b c d x.val (affineXorNat n a b c d x.val) rfl
  have hy := affine_xor_congruence n a b c d y.val (affineXorNat n a b c d x.val) he.symm
  apply Fin.ext
  exact triangular_lift_unique n ((b:ℤ)-a) 1 ((d:ℤ)-c) hab
    (fun z => (a*z+c)&&&affineXorNat n a b c d x.val)
    (fun u v j h => affine_mask_prefix a c _ u v j h)
    x.val y.val x.isLt y.isLt (by simpa only [mul_one] using hx.trans hy.symm)
-- CHECKPOINT

end ProvenHashes.UMASH
