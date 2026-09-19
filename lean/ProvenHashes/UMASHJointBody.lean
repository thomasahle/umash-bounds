import ProvenHashes.UMASHJointPrefixes

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype maskSet

theorem probability_and_update_event_le {I V : Type*} [Fintype I] [Fintype V]
    [Nonempty V] [DecidableEq I] (E F : (I → V) → Prop) (i : I) (c : ℚ≥0)
    (hE : ∀ k v, E (Function.update k i v) ↔ E k)
    (hs : ∀ k, E k → uniformProb (fun v => F (Function.update k i v)) ≤ c) :
    uniformProb (fun k => E k ∧ F k) ≤ uniformProb E*c := by
  let G := fun k => E k ∧ F k
  have hG (k : I → V) : uniformProb (fun v => G (Function.update k i v)) ≤ c := by
    by_cases hk : E k
    · have he : (fun v => G (Function.update k i v)) =
          (fun v => F (Function.update k i v)) := by
        funext v
        apply propext
        simp only [G, hE k v, hk, true_and]
      rw [he]
      exact hs k hk
    · have he : (fun v => G (Function.update k i v)) = (fun _ => False) := by
        funext v
        apply propext
        simp only [G, hE k v, hk, false_and]
      rw [he]
      simp [uniformProb]
  have h := probability_and_update_le E G i c hE hG
  have he : (fun k => E k ∧ G k) = (fun k => E k ∧ F k) := by
    funext k
    exact propext (by dsimp only [G]; tauto)
  rwa [he] at h
-- CHECKPOINT

theorem body_xor_eq_primary (k : OHKey) (seed : Word) (x y : Block)
    (hx : x.chunks ≠ []) (hy : y.chunks ≠ [])
    (hp : x.chunks.dropLast = y.chunks.dropLast) :
    xorChunk (secondaryBody k x seed) (secondaryBody k y seed) =
      xorChunk (oh k x seed) (oh k y seed) := by
  let xs := x.chunks.dropLast
  have hxs : x.chunks = xs ++ [lastChunk x] := block_chunks_split x hx
  have hys : y.chunks = xs ++ [lastChunk y] := by
    dsimp only [xs]
    rw [hp]
    exact block_chunks_split y hy
  rw [secondaryBody_append_last k x seed xs (lastChunk x) hxs,
    secondaryBody_append_last k y seed xs (lastChunk y) hys,
    oh_append_last k x seed xs (lastChunk x) hxs, oh_append_last k y seed xs (lastChunk y) hys]
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i _ <;>
    simp [xorChunk, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

theorem secondaryBody_low_prefix (k : OHKey) (seed : Word) (x y : Block)
    (hx : x.chunks ≠ []) (hy : y.chunks ≠ [])
    (hp : x.chunks.dropLast = y.chunks.dropLast) (r : ℕ) (hr : r ≤ 64)
    (h1 : 2^r ∣ ((lastChunk x).1 ^^^ (lastChunk y).1).toNat)
    (h2 : 2^r ∣ ((lastChunk x).2 ^^^ (lastChunk y).2).toNat) :
    2^r ∣ ((secondaryBody k x seed).1 ^^^ (secondaryBody k y seed).1).toNat := by
  let xs := x.chunks.dropLast
  have hxs : x.chunks = xs ++ [lastChunk x] := block_chunks_split x hx
  have hys : y.chunks = xs ++ [lastChunk y] := by
    dsimp only [xs]
    rw [hp]
    exact block_chunks_split y hy
  apply (word_prefix_eq_iff_xor_dvd _ _ r).mp
  rw [secondaryBody_append_last k x seed xs (lastChunk x) hxs,
    secondaryBody_append_last k y seed xs (lastChunk y) hys]
  simp only [xorChunk, BitVec.toNat_xor, Nat.xor_mod_two_pow]
  rw [enh_low_prefix (lastChunk x) (lastChunk y) (keyPair k xs.length)
    (blockTag seed x) (blockTag seed y) r hr h1 h2]
-- CHECKPOINT

theorem primary_event_implies_body_low_eq (k : OHKey) (seed : Word) (x y : Block)
    (hx : x.chunks ≠ []) (hy : y.chunks ≠ [])
    (hp : x.chunks.dropLast = y.chunks.dropLast)
    (h1 : 16 ∣ ((lastChunk x).1 ^^^ (lastChunk y).1).toNat)
    (h2 : 16 ∣ ((lastChunk x).2 ^^^ (lastChunk y).2).toNat)
    (he : primaryEvent seed x y k) :
    (secondaryBody k x seed).1 = (secondaryBody k y seed).1 := by
  have hxor := congrArg (fun c : Chunk => c.1.toNat) (body_xor_eq_primary k seed x y hx hy hp)
  dsimp only at hxor
  have hm : ((secondaryBody k x seed).1 ^^^ (secondaryBody k y seed).1).toNat ∈ maskSet := by
    change (xorChunk (secondaryBody k x seed) (secondaryBody k y seed)).1.toNat ∈ maskSet
    rw [hxor]
    simpa only [xorChunk, BitVec.toNat_xor] using
      (Finset.mem_product.mp (project_eq_mask_cover (oh k x seed) (oh k y seed) he)).1
  have hdiv := secondaryBody_low_prefix k seed x y hx hy hp 4 (by decide) h1 h2
  have hf : ((secondaryBody k x seed).1 ^^^ (secondaryBody k y seed).1).toNat ∈
      maskSet.filter (fun d => d%16 = 0) :=
    Finset.mem_filter.mpr ⟨hm, Nat.mod_eq_zero_of_dvd hdiv⟩
  rw [maskSet_mod_sixteen, Finset.mem_singleton] at hf
  apply BitVec.xor_eq_zero_iff.mp
  apply BitVec.eq_of_toNat_eq
  simpa only [BitVec.toNat_zero] using hf
-- CHECKPOINT

end ProvenHashes.UMASH
