import ProvenHashes.UMASHWordValuation

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype enh ph clmul

/-- Translate a keyed operand to the first message's uniform word, with
the second message represented by its wrapped increment. -/
theorem word_add_increment_toNat (a b k : Word) :
    (b+k).toNat = ((a+k).toNat+(b-a).toNat)%q := by
  have he : b+k = (a+k)+(b-a) := by abel
  rw [he, BitVec.toNat_add]
  rfl
-- CHECKPOINT

/-- The literal low ENH difference is exactly the counted modular-product
XOR after translating the two independent key words. -/
theorem enh_low_xor_to_operands (k x y : Chunk) (tag tag' : Word) :
    ((enh k x tag).1 ^^^ (enh k y tag').1).toNat =
      lowENHXor 64 (y.1-x.1).toNat (y.2-x.2).toNat
        (x.1+k.1).toNat (x.2+k.2).toNat := by
  have hx := congrArg Prod.fst (enh_toNat k x tag)
  have hy := congrArg Prod.fst (enh_toNat k y tag')
  dsimp only at hx hy
  rw [BitVec.toNat_xor, hx, hy, word_add_increment_toNat x.1 y.1 k.1,
    word_add_increment_toNat x.2 y.2 k.2]
  simp only [lowENHXor, q, Nat.mod_mul_mod, Nat.mul_mod_mod]
-- CHECKPOINT

/-- PROOF2 Lemma 5.2 on the literal keyed ENH low word, with its original
XOR valuation and only the trimmed positive-valuation hypothesis. -/
theorem enh_low_xor_target_probability (x y : Chunk) (tag tag' e : Word)
    (hx : x.1 ≠ y.1) (hy : x.2 ≠ y.2) (r : ℕ)
    (hr : r = min (wordValuation x.1 y.1) (wordValuation x.2 y.2))
    (hr1 : 1 ≤ r) (he : 2^r ∣ e.toNat) :
    uniformProb (fun k : Chunk => (enh k x tag).1 ^^^ (enh k y tag').1 = e) ≤
      lowTargetK r e.toNat/q := by
  have hn (a b : Word) (hab : a ≠ b) : 0 < (b-a).toNat := by
    apply Nat.pos_of_ne_zero
    intro h
    have hz : b-a = 0 := BitVec.eq_of_toNat_eq h
    exact hab (sub_eq_zero.mp hz).symm
  let trans : Chunk ≃ Chunk := Equiv.prodCongr (Equiv.addLeft x.1) (Equiv.addLeft x.2)
  let E (ab : Chunk) : Prop :=
    lowENHXor 64 (y.1-x.1).toNat (y.2-x.2).toNat ab.1.toNat ab.2.toNat = e.toNat
  calc
    _ ≤ uniformProb (fun k : Chunk => E (trans k)) := by
      apply probability_mono
      intro k hk
      have ht := congrArg BitVec.toNat hk
      rw [enh_low_xor_to_operands] at ht
      exact ht
    _ = uniformProb E := uniformProb_equiv trans E
    _ ≤ _ := low_enh_target_bound (y.1-x.1).toNat (y.2-x.2).toNat r e.toNat
      (hn _ _ hx) (y.1-x.1).isLt (hn _ _ hy) (y.2-x.2).isLt
      (by simpa only [wordValuation_eq_sub _ _ hx, wordValuation_eq_sub _ _ hy] using hr)
      hr1 e.isLt he
-- CHECKPOINT

/-- PROOF2 Lemma 4.3 on the literal folded ENH high word. Equality of the
low words removes the fold before applying the proved high-target count. -/
theorem enh_high_xor_target_probability (x y : Chunk) (tag tag' e : Word)
    (hx : x.1 ≠ y.1) (hy : x.2 ≠ y.2) :
    uniformProb (fun k : Chunk => (enh k x tag).1 = (enh k y tag').1 ∧
      (enh k x tag).2 ^^^ (enh k y tag').2 = e) ≤ highTargetK e.toNat/q := by
  have hn (a b : Word) (hab : a ≠ b) : 0 < (b-a).toNat := by
    apply Nat.pos_of_ne_zero
    intro h
    have hz : b-a = 0 := BitVec.eq_of_toNat_eq h
    exact hab (sub_eq_zero.mp hz).symm
  let trans : Chunk ≃ Chunk := Equiv.prodCongr (Equiv.addLeft x.1) (Equiv.addLeft x.2)
  let E (ab : Chunk) : Prop := highXorEventNat 64 (y.1-x.1).toNat (y.2-x.2).toNat
    tag.toNat tag'.toNat e.toNat (ab.1.toNat,ab.2.toNat)
  calc
    _ ≤ uniformProb (fun k : Chunk => E (trans k)) := by
      apply probability_mono
      intro k hk
      have hl := congrArg BitVec.toNat hk.1
      have hh := congrArg BitVec.toNat hk.2
      have hxl := congrArg Prod.fst (enh_toNat k x tag)
      have hyl := congrArg Prod.fst (enh_toNat k y tag')
      have hxh := congrArg Prod.snd (enh_toNat k x tag)
      have hyh := congrArg Prod.snd (enh_toNat k y tag')
      dsimp only at hxl hyl hxh hyh
      rw [hxl, hyl] at hl
      rw [BitVec.toNat_xor, hxh, hyh, ← hl] at hh
      have hcancel (a b c : ℕ) : (a ^^^ c) ^^^ (b ^^^ c) = a ^^^ b := by
        rw [Nat.xor_comm b c, Nat.xor_assoc, ← Nat.xor_assoc c c b,
          Nat.xor_self, Nat.zero_xor]
      rw [hcancel] at hh
      change highXorEventNat 64 (y.1-x.1).toNat (y.2-x.2).toNat
        tag.toNat tag'.toNat e.toNat ((x.1+k.1).toNat,(x.2+k.2).toNat)
      constructor
      · simpa only [word_add_increment_toNat x.1 y.1 k.1,
          word_add_increment_toNat x.2 y.2 k.2, q] using hl
      · simpa only [word_add_increment_toNat x.1 y.1 k.1,
          word_add_increment_toNat x.2 y.2 k.2, q] using hh
    _ = uniformProb E := uniformProb_equiv trans E
    _ ≤ _ := high_enh_target_bound _ _ _ _ _
      ⟨hn _ _ hx, (y.1-x.1).isLt⟩ ⟨hn _ _ hy, (y.2-x.2).isLt⟩
-- CHECKPOINT

end ProvenHashes.UMASH
