import ProvenHashes.UMASHOneWordBins
import ProvenHashes.UMASHLowTargetSparse

/-! Scaled coordinates for the one-word ENH argument from the GPT-6 Pro
handoff of 2026-09-19, earlier ENH notes §4. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

theorem one_word_shift_coordinates (M N A α : ℕ) (hM : 0 < M) :
    ((A+M*α)%(M*N))%M = A%M ∧
    ((A+M*α)%(M*N))/M = (A/M+α)%N := by
  constructor
  · rw [Nat.mod_mul_right_mod, Nat.add_mul_mod_self_left]
  · rw [Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ hM]
-- CHECKPOINT

theorem one_word_low_multiple (n v δ A B : ℕ) (hv : v ≤ n)
    (hd : 2^v ∣ δ) (ho : (δ/2^v)%2 = 1)
    (he : A*B%2^n = ((A+δ)%2^n)*B%2^n) : 2^(n-v) ∣ B := by
  let M := 2^v
  let N := 2^(n-v)
  have hMN : M*N = 2^n := by dsimp [M,N]; rw [← pow_add,Nat.add_sub_of_le hv]
  have hd' : δ = M*(δ/M) := (Nat.mul_div_cancel' hd).symm
  have hm : Nat.ModEq (2^n) (A*B+0) (A*B+δ*B) := by
    simpa only [Nat.add_zero,Nat.mod_mul_mod,Nat.add_mul] using he
  have hz : 2^n ∣ δ*B := Nat.dvd_of_mod_eq_zero (Nat.ModEq.add_left_cancel' (A*B) hm).symm
  rw [hd',← hMN,Nat.mul_assoc] at hz
  have hc : N.Coprime (δ/M) :=
    (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ho)).pow_left (n-v)
  exact hc.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left (by positivity : 0 < M) hz)
-- CHECKPOINT

theorem scaled_product_high (M N A z : ℕ) (hM : 0 < M) (hN : 0 < N) :
    A*(N*z)/(M*N) = A/M*z + A%M*z/M := by
  calc
    _ = A*z/M := by rw [show A*(N*z) = A*z*N by ring, Nat.mul_div_mul_right _ _ hN]
    _ = (A%M*z+M*(A/M*z))/M := by congr 1; nlinarith [Nat.mod_add_div A M]
    _ = _ := by rw [Nat.add_mul_div_left _ _ hM]; omega
-- CHECKPOINT

theorem one_word_next_odd (n v α : ℕ) (hv : v < n) (ho : α%2 = 1) (j : ℕ) :
    ((((j+α)%2^(n-v):ℕ):ℤ)-j)%2 = 1 := by
  have hd : 2 ∣ 2^(n-v) := dvd_pow_self 2 (by omega : n-v ≠ 0)
  have hh : ((j+α)%2^(n-v))%2 = (j%2+1)%2 := by
    rw [Nat.mod_mod_of_dvd _ hd, Nat.add_mod, ho]
  omega
-- CHECKPOINT

theorem one_word_event_to_coordinates (n v δ tag tag' e A B : ℕ)
    (hv : v ≤ n) (hd : 2^v ∣ δ) (hB : B < 2^n) (hdiv : 2^(n-v) ∣ B)
    (he : highXorEventNat n δ 0 tag tag' e (A,B)) :
    oneWordCoordinateEvent n v (fun j => (j+δ/2^v)%2^(n-v)) tag tag' e (A,B/2^(n-v)) := by
  let M := 2^v
  let N := 2^(n-v)
  have hM : 0 < M := by positivity
  have hN : 0 < N := by positivity
  have hMN : M*N = 2^n := by dsimp [M,N]; rw [← pow_add,Nat.add_sub_of_le hv]
  have hd' : δ = M*(δ/M) := (Nat.mul_div_cancel' hd).symm
  have hB' : B = N*(B/N) := (Nat.mul_div_cancel' hdiv).symm
  have hs := one_word_shift_coordinates M N A (δ/M) hM
  rw [← hd', hMN] at hs
  have hh := he.2
  simp only [Nat.add_zero, Nat.mod_eq_of_lt hB] at hh
  have hp (a : ℕ) : a*B/2^n = a/M*(B/N) + a%M*(B/N)/M := by
    conv_lhs => rw [hB',← hMN]
    exact scaled_product_high M N a (B/N) hM hN
  rw [hp,hp,hs.1,hs.2] at hh
  simpa only [oneWordCoordinateEvent, affineXorNat, M, N, Nat.add_assoc] using hh
-- CHECKPOINT

end ProvenHashes.UMASH
