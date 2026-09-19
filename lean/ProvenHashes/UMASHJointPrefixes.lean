import ProvenHashes.UMASHLowPHDistribution
import ProvenHashes.UMASHJointENH
import ProvenHashes.UMASHOddPHSlice

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

theorem word_prefix_eq_iff_xor_dvd (x y : Word) (r : ℕ) :
    x.toNat%2^r = y.toNat%2^r ↔ 2^r ∣ (x ^^^ y).toNat := by
  rw [Nat.dvd_iff_mod_eq_zero, BitVec.toNat_xor, Nat.xor_mod_two_pow]
  constructor
  · intro h
    rw [h, Nat.xor_self]
  · intro h
    have he := congrArg (fun n => n ^^^ (y.toNat%2^r)) h
    simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using he
-- CHECKPOINT

theorem clmul_both_preserves_prefix (a b a' b' : Word) (r : ℕ)
    (ha : a.toNat%2^r = a'.toNat%2^r) (hb : b.toNat%2^r = b'.toNat%2^r) :
    (clmul a b).toNat%2^r = (clmul a' b').toNat%2^r := by
  calc
    _ = (clmul a b').toNat%2^r := clmul_preserves_prefix a b b' r hb
    _ = (clmul b' a).toNat%2^r := by rw [clmul_comm a b']
    _ = (clmul b' a').toNat%2^r := clmul_preserves_prefix b' a a' r ha
    _ = _ := by rw [clmul_comm b' a']
-- CHECKPOINT

theorem ph_low_prefix (x y k : Chunk) (r : ℕ) (hr : r ≤ 64)
    (hx : 2^r ∣ (x.1 ^^^ y.1).toNat) (hy : 2^r ∣ (x.2 ^^^ y.2).toNat) :
    (ph k x).1.toNat%2^r = (ph k y).1.toNat%2^r := by
  have h1 := (word_prefix_eq_iff_xor_dvd x.1 y.1 r).mpr hx
  have h2 := (word_prefix_eq_iff_xor_dvd x.2 y.2 r).mpr hy
  have ha : (x.1 ^^^ k.1).toNat%2^r = (y.1 ^^^ k.1).toNat%2^r := by
    rw [BitVec.toNat_xor, BitVec.toNat_xor, Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, h1]
  have hb : (x.2 ^^^ k.2).toNat%2^r = (y.2 ^^^ k.2).toNat%2^r := by
    rw [BitVec.toNat_xor, BitVec.toNat_xor, Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, h2]
  simpa only [ph, split, BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hr)] using
    clmul_both_preserves_prefix _ _ _ _ r ha hb
-- CHECKPOINT

theorem enh_low_prefix (x y k : Chunk) (t t' : Word) (r : ℕ) (hr : r ≤ 64)
    (hx : 2^r ∣ (x.1 ^^^ y.1).toNat) (hy : 2^r ∣ (x.2 ^^^ y.2).toNat) :
    (enh k x t).1.toNat%2^r = (enh k y t').1.toNat%2^r := by
  have h1 := (word_prefix_eq_iff_xor_dvd x.1 y.1 r).mpr hx
  have h2 := (word_prefix_eq_iff_xor_dvd x.2 y.2 r).mpr hy
  have hf (a b c : Word) (h : a.toNat%2^r = b.toNat%2^r) :
      (a+c).toNat%2^r = (b+c).toNat%2^r := by
    simp only [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hr),
      Nat.add_mod, h, Nat.mod_mod]
  have hL := congrArg Prod.fst (enh_toNat k x t)
  have hL' := congrArg Prod.fst (enh_toNat k y t')
  dsimp only at hL hL'
  have hq : 2^r ∣ q := pow_dvd_pow 2 hr
  simp only [hL, hL', Nat.mod_mod_of_dvd _ hq, Nat.mul_mod,
    hf x.1 y.1 k.1 h1, hf x.2 y.2 k.2 h2, Nat.mod_mod]
-- CHECKPOINT

theorem checksum_xor_of_prefix (k : OHKey) (x y : Block)
    (hx : x.chunks ≠ []) (hy : y.chunks ≠ [])
    (hp : x.chunks.dropLast = y.chunks.dropLast) :
    xorChunk (checksum k x) (checksum k y) = xorChunk (lastChunk x) (lastChunk y) := by
  rw [checksum_append_last k x _ _ (block_chunks_split x hx),
    checksum_append_last k y _ _ (block_chunks_split y hy), ← hp]
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i _ <;>
    simp [xorChunk, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

def secondaryPrefix (k : OHKey) (xs : List Chunk) : Chunk :=
  (xs.mapIdx (fun i x => shuffle (ph (keyPair k i) x) (i+1) (xs.length+1))).foldl xorChunk (0,0)

theorem secondaryBody_append_last (k : OHKey) (b : Block) (seed : Word)
    (xs : List Chunk) (last : Chunk) (hb : b.chunks = xs ++ [last]) :
    secondaryBody k b seed = xorChunk (secondaryPrefix k xs)
      (enh (keyPair k xs.length) last (blockTag seed b)) := by
  have hm : mixed k b seed =
      xs.mapIdx (fun i x => ph (keyPair k i) x) ++
        [enh (keyPair k xs.length) last (blockTag seed b)] := by
    simp only [mixed, hb, List.mapIdx_append_one, List.length_append,
      List.length_singleton, Nat.lt_irrefl, ↓reduceIte]
    congr 1
    apply List.mapIdx_eq_mapIdx_iff.mpr
    intro i hi
    simp only [show i+1 < xs.length+1 from by omega, ↓reduceIte]
  simp only [secondaryBody, hm, List.mapIdx_append_one, List.length_mapIdx,
    hb, List.length_append, List.length_singleton, shuffle, Nat.sub_self,
    ↓reduceIte, List.foldl_append, List.foldl_cons, List.foldl_nil, secondaryPrefix]
  congr 1
  congr 1
  ext i hi
  simp
-- CHECKPOINT

end ProvenHashes.UMASH
