import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyBlock

/-!
# A component letter of a rotation carries one of the design's exponents

`HullSC.exists_block_of_long_prefix_rotate` finds a block letter and hands back
its exponent, because it chose the position.  The matched letter on the other
side is not chosen: it arrives as a component start of the quadrilateral, is
carried to a letter of the side by
`GGT.OsinComponents.exists_comp_of_isCompStart_rev`, and all that is known of it
is that it reads `comp b x` for some `x`.  The closers want it in the design's
own shape --- `x = (if b then h₁ else h₀) ^ e` with `e ∈ ms` --- and that is
what these two lemmas supply.

The content is the same in both directions and is already in the tree: a
position of a rotation is a position of the word modulo the length
(`HullSC.getElem?_of_rotate`), a position of the relator carrying an index is a
position of the run (`HullSC.blockIndex_of_relatorWord₂`, and
`blockIndex_of_revInv_relatorWord₂` on the other side), and a position of the
run carries the exponent the list holds there
(`HullSC.blockWord_getElem?_exponent`, and its mirrored twin).  What is new is
only that they are composed at a position the caller did not choose.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Exponent

variable {G : Type u} [Group G]

/-- **A component letter of a rotation of the relator carries one of the
design's exponents.** -/
theorem exponent_of_comp_rotate {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    {c d : ℕ} {b : Bool} {x : G}
    (hd : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
      = some (GGT.RelLetter.comp b x)) :
    ∃ e : ℕ, e ∈ ms ∧ x = (if b then h₁ else h₀) ^ e := by
  have hlenW : ((relatorWord₂ p h₀ h₁ ms).rotate c).length
      = (relatorWord₂ p h₀ h₁ ms).length := by
    rw [List.length_rotate]
  obtain ⟨hdW, -⟩ := List.getElem?_eq_some_iff.mp hd
  have hdR : d < (relatorWord₂ p h₀ h₁ ms).length := by omega
  have hR := getElem?_of_rotate hdR hd
  obtain ⟨i₀, -, -, hbi⟩ := blockIndex_of_relatorWord₂ hR
  obtain ⟨m, hm, hxm⟩ :=
    blockWord_getElem?_exponent h₀ h₁ false ms i₀ b x hbi
  exact ⟨m, List.mem_of_getElem? hm, hxm⟩

/-- **The mirrored form.**  In the formal inverse the letters carry inverses. -/
theorem exponent_of_comp_rotate_revInv {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    {c d : ℕ} {b : Bool} {x : G}
    (hd : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c)[d]?
      = some (GGT.RelLetter.comp b x)) :
    ∃ e : ℕ, e ∈ ms ∧ x = ((if b then h₁ else h₀) ^ e)⁻¹ := by
  have hlenW : ((RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).rotate c).length
      = (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by
    rw [List.length_rotate]
  obtain ⟨hdW, -⟩ := List.getElem?_eq_some_iff.mp hd
  have hdR : d < (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length := by omega
  have hR := getElem?_of_rotate hdR hd
  obtain ⟨t, htv⟩ :
      ∃ t : ℕ,
        (c + d) % (RelWord.revInv (relatorWord₂ p h₀ h₁ ms)).length = t :=
    ⟨_, rfl⟩
  rw [htv] at hR
  obtain ⟨ht, hbi⟩ := blockIndex_of_revInv_relatorWord₂ hR
  have hq : t + (ms.length - 1 - t) + 1 = ms.length := by omega
  obtain ⟨m, hm, hxm⟩ :=
    revInv_blockWord_getElem?_exponent h₀ h₁ false ms hq hbi
  exact ⟨m, List.mem_of_getElem? hm, hxm⟩

end Exponent

end HullSC
end GroupApproximation
