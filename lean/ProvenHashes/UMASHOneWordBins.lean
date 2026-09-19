import ProvenHashes.UMASHOneWordAffine

/-! Dyadic counting for the one-word zero-low ENH atom. The argument from
the GPT-6 Pro handoff of 2026-09-19, earlier ENH notes §4, labels a solution
by its high operand digit, product quotient, and a short residue. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def oneWordCoordinateEvent (n v : ℕ) (next : ℕ → ℕ) (tag tag' e : ℕ) (az : ℕ × ℕ) : Prop :=
  affineXorNat n (az.1/2^v) (next (az.1/2^v))
    ((az.1%2^v)*az.2/2^v+tag) ((az.1%2^v)*az.2/2^v+tag') az.2 = e

theorem one_word_coordinate_bin_count (n v b : ℕ) (hv : v ≤ n) (hb : b < v)
    (next : ℕ → ℕ) (tag tag' e : ℕ)
    (hodd : ∀ j < 2^(n-v), ((next j:ℤ)-j)%2 = 1)
    (S : Finset (ℕ × ℕ))
    (hbox : ∀ az ∈ S, az.1 < 2^n ∧ az.2 ∈ Finset.Ico (2^b) (2^(b+1)))
    (hevent : ∀ az ∈ S, oneWordCoordinateEvent n v next tag tag' e az) :
    S.card ≤ 2*2^n := by
  let M := 2^v
  let N := 2^(n-v)
  let R := 2^(v-b)
  have hM : 0 < M := by dsimp [M]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hMN : M*N = 2^n := by dsimp [M,N]; rw [← pow_add,Nat.add_sub_of_le hv]
  have hscale : 2^b*R = M := by dsimp [R,M]; rw [← pow_add,Nat.add_sub_of_le hb.le]
  let label (az : ℕ × ℕ) := (az.1/M, ((az.1%M)*az.2/M, az.1%M%R))
  have hc : S.card ≤ ((Finset.range N) ×ˢ ((Finset.range (2^(b+1))) ×ˢ (Finset.range R))).card := by
    apply Finset.card_le_card_of_injOn label
    · intro az haz
      have h := hbox az haz
      have hz := Finset.mem_Ico.mp h.2
      have hzp : 0 < az.2 := lt_of_lt_of_le (by positivity) hz.1
      have hu : az.1%M < M := Nat.mod_lt _ hM
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_range.mpr ?_, Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr (Nat.mod_lt _ hR)⟩⟩
      · change az.1/M < N
        apply (Nat.div_lt_iff_lt_mul hM).mpr
        simpa only [Nat.mul_comm N M,hMN] using h.1
      · change (az.1%M)*az.2/M < 2^(b+1)
        apply lt_trans _ hz.2
        apply (Nat.div_lt_iff_lt_mul hM).mpr
        simpa only [Nat.mul_comm az.2 M] using Nat.mul_lt_mul_of_pos_right hu hzp
    · intro az haz az' haz' he
      have hx := hbox az haz
      have hy := hbox az' haz'
      have hJ : az.1/M = az'.1/M := congrArg Prod.fst he
      have hC : az.1%M*az.2/M = az'.1%M*az'.2/M := congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.1) he
      have hU : az.1%M%R = az'.1%M%R := congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.2) he
      have hj : az.1/M < N := (Nat.div_lt_iff_lt_mul hM).mpr (by
        simpa only [Nat.mul_comm N M,hMN] using hx.1)
      have hzbound : ∀ z, z ∈ Finset.Ico (2^b) (2^(b+1)) → z < 2^n := by
        intro z hz
        exact (Finset.mem_Ico.mp hz).2.trans_le (pow_le_pow_right₀ (by decide : 1 ≤ (2:ℕ)) (by omega))
      have hz : az.2 = az'.2 := by
        have h₁ := hevent az haz
        have h₂ := hevent az' haz'
        change affineXorNat n (az.1/M) (next (az.1/M))
          (az.1%M*az.2/M+tag) (az.1%M*az.2/M+tag') az.2 = e at h₁
        change affineXorNat n (az'.1/M) (next (az'.1/M))
          (az'.1%M*az'.2/M+tag) (az'.1%M*az'.2/M+tag') az'.2 = e at h₂
        rw [← hJ,← hC] at h₂
        exact congrArg Fin.val (affine_xor_odd_injective n (az.1/M) (next (az.1/M))
          _ _ (hodd _ hj) (a₁ := ⟨az.2,hzbound _ hx.2⟩) (a₂ := ⟨az'.2,hzbound _ hy.2⟩)
          (h₁.trans h₂.symm))
      have hMR : M ≤ az.2*R := by
        rw [← hscale]
        exact Nat.mul_le_mul_right R (Finset.mem_Ico.mp hx.2).1
      have hu : az.1%M = az'.1%M :=
        mul_div_residue_injective M az.2 R (az.1%M*az.2/M) hM hMR _ _
          (by rw [Nat.mul_comm]) (by simpa only [Nat.mul_comm, ← hz] using hC.symm) hU
      apply Prod.ext _ hz
      have ha := Nat.mod_add_div az.1 M
      have hb := Nat.mod_add_div az'.1 M
      rw [hu,hJ] at ha
      omega
  apply hc.trans_eq
  rw [Finset.card_product,Finset.card_product,Finset.card_range,Finset.card_range,Finset.card_range]
  calc
    N*(2^(b+1)*R) = 2*(M*N) := by
      rw [pow_succ]
      calc
        _ = 2*((2^b*R)*N) := by ring
        _ = _ := by rw [hscale]
    _ = _ := by rw [hMN]
-- CHECKPOINT

/-- Sum the v dyadic bins and the zero multiplier separately. -/
theorem one_word_coordinate_count (n v : ℕ) (hv : v ≤ n)
    (next : ℕ → ℕ) (tag tag' e : ℕ)
    (hodd : ∀ j < 2^(n-v), ((next j:ℤ)-j)%2 = 1)
    (S : Finset (ℕ × ℕ))
    (hbox : ∀ az ∈ S, az.1 < 2^n ∧ az.2 < 2^v)
    (hevent : ∀ az ∈ S, oneWordCoordinateEvent n v next tag tag' e az) :
    S.card ≤ (2*v+1)*2^n := by
  let f (z : ℕ) := (S.filter (fun az => az.2 = z)).card
  have hcard : S.card = ∑ z ∈ Finset.range (2^v), f z :=
    Finset.card_eq_sum_card_fiberwise (fun az haz => Finset.mem_range.mpr (hbox az haz).2)
  have hz : f 0 ≤ 2^n := by
    calc
      _ ≤ (Finset.range (2^n)).card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · intro az haz
          exact Finset.mem_range.mpr (hbox az (Finset.mem_filter.mp haz).1).1
        · intro az haz az' haz' he
          exact Prod.ext he ((Finset.mem_filter.mp haz).2.trans (Finset.mem_filter.mp haz').2.symm)
      _ = _ := Finset.card_range _
  have hbins (b : ℕ) (hb : b < v) : ∑ z ∈ Finset.Ico (2^b) (2^(b+1)), f z ≤ 2*2^n := by
    change (∑ z ∈ Finset.Ico (2^b) (2^(b+1)), (S.filter (fun az => az.2 = z)).card) ≤ _
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    apply one_word_coordinate_bin_count n v b hv hb next tag tag' e hodd
    · intro az haz
      have hmem := Finset.mem_filter.mp haz
      exact ⟨(hbox az hmem.1).1,hmem.2⟩
    · intro az haz
      exact hevent az (Finset.mem_filter.mp haz).1
  rw [hcard, ← Finset.sum_range_add_sum_Ico f (Nat.one_le_two_pow (n := v)), Finset.sum_range_one]
  calc
    _ ≤ 2^n+v*(2*2^n) := Nat.add_le_add hz (dyadic_sum_bound f (2*2^n) v hbins)
    _ = _ := by ring
-- CHECKPOINT

end ProvenHashes.UMASH
