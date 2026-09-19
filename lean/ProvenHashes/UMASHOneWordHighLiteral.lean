import ProvenHashes.UMASHOneWordHighCount
import ProvenHashes.UMASHENHTargetWords

/-! Literal-word form of the one-word high atom, using the argument from
the GPT-6 Pro handoff of 2026-09-19, earlier ENH notes §4. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype enh ph clmul

theorem enh_high_one_word_left_probability (x y : Chunk) (tag tag' e : Word)
    (hx : x.1 ≠ y.1) (hy : x.2 = y.2) :
    uniformProb (fun k : Chunk => (enh k x tag).1 = (enh k y tag').1 ∧
      (enh k x tag).2 ^^^ (enh k y tag').2 = e) ≤ (127:ℚ≥0)/q := by
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
    _ ≤ _ := by
      have hε : (y.2-x.2).toNat = 0 := by rw [hy,sub_self]; rfl
      simpa only [E,hε] using one_word_high_probability_word (y.1-x.1).toNat
        tag.toNat tag'.toNat e.toNat ⟨hn _ _ hx,(y.1-x.1).isLt⟩
-- CHECKPOINT

theorem enh_high_one_word_probability (x y : Chunk) (tag tag' e : Word)
    (he : (x.1 ≠ y.1 ∧ x.2 = y.2) ∨ (x.1 = y.1 ∧ x.2 ≠ y.2)) :
    uniformProb (fun k : Chunk => (enh k x tag).1 = (enh k y tag').1 ∧
      (enh k x tag).2 ^^^ (enh k y tag').2 = e) ≤ (127:ℚ≥0)/q := by
  rcases he with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact enh_high_one_word_left_probability x y tag tag' e hx hy
  · rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => (enh k x tag).1 = (enh k y tag').1 ∧
        (enh k x tag).2 ^^^ (enh k y tag').2 = e)]
    simpa only [enh,BitVec.mul_comm] using
      enh_high_one_word_left_probability (x.2,x.1) (y.2,y.1) tag tag' e hy hx
-- CHECKPOINT

end ProvenHashes.UMASH
