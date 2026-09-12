import GroupApproximation.GGT.HullSCRelatorSeparation2MirrorGap

/-!
# The aligned cases of step (c), with the offsets no longer assumed equal

`HullSC.rotate_eq_of_block_at_offset₂` and its mirrored twin close the two
aligned cases -- both members rotations of the relator, or both rotations of its
formal inverse -- from a block matched at the **same** offset in the two words.
The polygon estimate does not give the same offset: it gives two offsets pinned
to within `ε + 1` of each other.  So the conclusion has to be restated, and the
restatement is sharper than the old one rather than weaker:

  `w.rotate i = w'.rotate j`

for a block of `w` at offset `i` matched with a block of `w'` at offset `j`.  At
`i = j` this is `w = w'` by injectivity of rotation, which is what step (b)
concluded; at `i ≠ j` it says the two members are rotations of one another by
`j - i`, which is Olshanskii's global translation and is where the conclusion of
the separation is proved rather than refuted.

The proof is the same identity as in the mirrored case, with the sign flipped:
matched blocks carry the same exponent, repetition-freeness turns that into the
same run index, and the run index determines the position, so
`(c + i) % n = (c' + j) % n`.  Then `List.rotate_mod` and `List.rotate_rotate`
turn an equality of positions into an equality of words.

The two mixed cases are `HullSC.not_mirroredMatch_of_gap`; the second of them --
the relator against the formal inverse in the other order -- is the same lemma
with the two words exchanged, since the identity it proves is symmetric in the
two summands.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Aligned

variable {G : Type u} [Group G]

/-- **Two matched blocks of two rotations of the relator sit at the same
position.** -/
theorem position_eq_of_alignedMatch {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ a : Bool,
      Function.Injective (fun k : ℕ => (if a then h₁ else h₀) ^ k))
    (hnodup : ms.Nodup) {c c' i j : ℕ}
    (hi : i < (relatorWord₂ p h₀ h₁ ms).length)
    (hj : j < (relatorWord₂ p h₀ h₁ ms).length)
    {b b' : Bool} {e f : ℕ} (hef : e = f)
    (hxi : ((relatorWord₂ p h₀ h₁ ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then h₁ else h₀) ^ e)))
    (hxj : ((relatorWord₂ p h₀ h₁ ms).rotate c')[j]?
      = some (GGT.RelLetter.comp b' ((if b' then h₁ else h₀) ^ f))) :
    (c + i) % (relatorWord₂ p h₀ h₁ ms).length
      = (c' + j) % (relatorWord₂ p h₀ h₁ ms).length := by
  have h1 := getElem?_of_rotate hi hxi
  have h2 := getElem?_of_rotate hj hxj
  obtain ⟨k, hkeq, hklt, hkb⟩ := blockIndex_of_relatorWord₂ h1
  obtain ⟨k', hk'eq, hk'lt, hk'b⟩ := blockIndex_of_relatorWord₂ h2
  obtain ⟨m, hm, hme⟩ := blockWord_getElem?_exponent h₀ h₁ false ms k b _ hkb
  obtain ⟨m', hm', hm'e⟩ :=
    blockWord_getElem?_exponent h₀ h₁ false ms k' b' _ hk'b
  have hem : e = m := hinj b hme
  have hfm : f = m' := hinj b' hm'e
  have hmm : m = m' := by omega
  rw [hmm] at hm
  have hkk : k = k' := getElem?_eq_of_nodup hnodup hm hm'
  omega

/-- **Two matched blocks of two rotations of the mirrored relator sit at the
same position.** -/
theorem position_eq_of_alignedMatch_revInv {p : List G} {h₀ h₁ : G}
    {ms : List ℕ}
    (hinj : ∀ a : Bool,
      Function.Injective (fun k : ℕ => (if a then h₁ else h₀) ^ k))
    (hnodup : ms.Nodup) {c c' i j : ℕ}
    (hi : i < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    (hj : j < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length)
    {b b' : Bool} {e f : ℕ} (hef : e = f)
    (hxi : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[i]?
      = some (GGT.RelLetter.comp b (((if b then h₁ else h₀) ^ e)⁻¹)))
    (hxj : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c')[j]?
      = some (GGT.RelLetter.comp b' (((if b' then h₁ else h₀) ^ f)⁻¹))) :
    (c + i) % (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      = (c' + j) % (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by
  have hrev : (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length
      = (relatorWord₂ p h₀ h₁ ms).length := RelWord.length_revInv _
  have h1 := getElem?_of_rotate hi hxi
  have h2 := getElem?_of_rotate hj hxj
  rw [hrev] at h1 h2
  obtain ⟨htlt, htb⟩ := blockIndex_of_revInv_relatorWord₂ h1
  obtain ⟨ht'lt, ht'b⟩ := blockIndex_of_revInv_relatorWord₂ h2
  obtain ⟨m, hm, hme⟩ :=
    revInv_blockWord_getElem?_exponent h₀ h₁ false ms
      (q := ms.length - 1 - (c + i) % (relatorWord₂ p h₀ h₁ ms).length)
      (by omega) htb
  obtain ⟨m', hm', hm'e⟩ :=
    revInv_blockWord_getElem?_exponent h₀ h₁ false ms
      (q := ms.length - 1 - (c' + j) % (relatorWord₂ p h₀ h₁ ms).length)
      (by omega) ht'b
  have hem : e = m := hinj b (inv_injective hme)
  have hfm : f = m' := hinj b' (inv_injective hm'e)
  have hmm : m = m' := by omega
  rw [hmm] at hm
  have hkk : ms.length - 1 - (c + i) % (relatorWord₂ p h₀ h₁ ms).length
      = ms.length - 1 - (c' + j) % (relatorWord₂ p h₀ h₁ ms).length :=
    getElem?_eq_of_nodup hnodup hm hm'
  rw [hrev]
  omega

/-- **Equal positions make the two members rotations of one another.**

At `i = j` this is `w = w'`, by injectivity of rotation; at `i ≠ j` it is the
global translation.  Stated for an arbitrary word, since neither the relator nor
its formal inverse is mentioned. -/
theorem rotate_eq_of_position_eq {α : Type*} (l : List α) {c c' i j : ℕ}
    (h : (c + i) % l.length = (c' + j) % l.length) :
    (l.rotate c).rotate i = (l.rotate c').rotate j := by
  rw [List.rotate_rotate, List.rotate_rotate,
    ← List.rotate_mod l (c + i), ← List.rotate_mod l (c' + j), h]

end Aligned

end HullSC
end GroupApproximation
