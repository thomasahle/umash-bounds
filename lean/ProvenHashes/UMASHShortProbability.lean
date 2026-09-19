import ProvenHashes.UMASHShortMixer

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem probability_prod_eq {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (E : A × B → Prop) (c : ℚ≥0)
    (hs : ∀ a, uniformProb (fun b => E (a,b)) = c) : uniformProb E = c := by
  have hc : (Fintype.card A : ℚ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [probability_prod]
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hc
-- CHECKPOINT

theorem probability_eq_of_update {I V : Type*} [Fintype I] [Fintype V]
    [Nonempty V] [DecidableEq I] (E : (I → V) → Prop) (i : I) (c : ℚ≥0)
    (hs : ∀ k, uniformProb (fun v => E (Function.update k i v)) = c) :
    uniformProb E = c := by
  classical
  let e := (Equiv.funSplitAt i V).trans (Equiv.prodComm _ _)
  let v₀ : V := Classical.choice inferInstance
  have hu (r : {j // j ≠ i} → V) (v : V) :
      e.symm (r,v) = Function.update (e.symm (r,v₀)) i v := by
    funext j
    by_cases hj : j = i
    · subst j; simp [e]
    · simp [e, Function.update, hj]
  rw [← uniformProb_equiv e.symm E]
  apply probability_prod_eq
  intro r
  have he : (fun v => E (e.symm (r,v))) =
      (fun v => E (Function.update (e.symm (r,v₀)) i v)) :=
    funext (fun v => congrArg E (hu r v))
  rw [he]
  exact hs (e.symm (r,v₀))
-- CHECKPOINT

theorem probability_bijective_point {V : Type*} [Fintype V]
    (f : V → V) (hf : Function.Bijective f) (t : V) :
    uniformProb (fun v => f v = t) = 1/(Fintype.card V : ℚ≥0) := by
  classical
  change uniformProb (fun v => (Equiv.ofBijective f hf) v = t) = _
  rw [uniformProb_equiv (Equiv.ofBijective f hf) (fun v => v = t)]
  have he : (Finset.univ.filter (fun v : V => v = t)) = {t} := by ext v; simp
  unfold uniformProb
  rw [he, Finset.card_singleton, Nat.cast_one]
-- CHECKPOINT

theorem shortHash_noise_bijective (seed : Word) (m : Message) (hm : m.length < 34)
    (k : OHKey) : Function.Bijective (fun v : Word =>
      shortHash (Function.update k ⟨m.length, hm⟩ v) seed m false) := by
  suffices hi : Function.Injective (fun v : Word =>
      shortHash (Function.update k ⟨m.length, hm⟩ v) seed m false) from
    ⟨hi, Finite.surjective_of_injective hi⟩
  intro a b hab
  simp only [shortHash_eq_mixer, keyWord_update k _ _ m.length hm,
    ↓reduceIte] at hab
  exact (BitVec.add_right_inj seed).mp
    ((BitVec.xor_right_inj (shortPrepare (shortPack m))).mp
      (shortFinish_injective hab))
-- CHECKPOINT

theorem short_message_uniform : ShortMessageUniform := by
  intro seed m hm t
  have hlen : m.length < 34 := by omega
  simpa only [word_card] using uniformProb_of_bijective_update
    (fun k => shortHash k seed m false) ⟨m.length, hlen⟩
    (shortHash_noise_bijective seed m hlen) t
-- CHECKPOINT

theorem short_different_length_collision : ShortDifferentLengthCollision := by
  intro seed x y hx hy hxy
  have hxl : x.length < 34 := by omega
  have hyl : y.length < 34 := by omega
  apply probability_eq_of_update _ (⟨x.length,hxl⟩ : Fin 34)
  intro k
  have hsame (v : Word) :
      shortHash (Function.update k ⟨x.length,hxl⟩ v) seed y false =
        shortHash k seed y false := by
    simp only [shortHash_eq_mixer, keyWord_update k _ v y.length hyl,
      show y.length ≠ x.length from Ne.symm hxy, ↓reduceIte]
  simp only [hsame]
  simpa only [word_card] using probability_bijective_point _
    (shortHash_noise_bijective seed x hxl k) (shortHash k seed y false)
-- CHECKPOINT

end ProvenHashes.UMASH
