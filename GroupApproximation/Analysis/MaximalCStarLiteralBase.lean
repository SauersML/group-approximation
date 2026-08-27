import GroupApproximation.Analysis.MaximalCStarProperCompression
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Kazhdan.KazhdanGenerators
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.MarkedCompressionProperness

/-!
# The base of `E` is such a pair

`Analysis/MaximalCStarParagraphEndpoint` proves the maximal-algebra consequence
for an arbitrary `StrictKazhdanCompression`.  The previously printed discussion
also named its concrete instance:
*"Let `G` contain a property-(T) subgroup `Γ` and an element `t` with
`t Γ t⁻¹ ⊊ Γ`; the base of `E` is such a pair."*  That aside is a claim about
the literal eight-generator group of Definition `def:E`, not about the chosen
presentation, and until now nothing exhibited the datum for it:
`Sofic/ChosenMaximalCStarInfinite` builds one for
`ChosenMarkedPresentation.MarkedGroup`, which is a different group.

This file builds the *datum* for the literal `E`, from pieces that are already
in the corpus; `Analysis/MaximalCStarParagraphEndpoint` imports it and states
the remark's conclusions at it, as the second conjunct of the badged
declaration `manuscriptMaximalCStarStrictCompressionRemark`.  The split is so
that this file can sit upstream of the endpoint: the endpoint is what draws the
conclusions, and it is what the manuscript cites.

The pieces:

* the compression datum itself is `LiteralNonMFEndpoint.inclusionData` — the
  base map `ι = baseMap`, the stable letter `t`, and the one-sided compression
  `t ι(Γ) t⁻¹ ⊆ ι(Γ)` of `stable_conjugates_base_into_base`;
* strictness is `MarkedCompressionProperness`: a nontrivial marked word
  certifies that `ι(a)` is missing from the compressed image, and the literal
  marked word is nontrivial by the Clifford witness
  (`LiteralNonMFLinearWitness.literal_mark_ne_one`);
* the Kazhdan pair is the literal base's own property `(T)`, from the P13
  bridge, lifted to representation universe `1` where the maximal algebra
  lives.

The last point is where the literal base differs from the chosen cover.  The
cover's property `(T)` is produced universe-polymorphically by the Shalom
construction, so `ChosenMaximalCStarInfinite` reads it off at universe `1`
directly.  The literal base has property `(T)` only at universe `0`, from the
exact P13 presentation — but `HasKazhdanPropertyT.liftUniverse` is the free
direction of universe transfer (a representation on a small Hilbert space is
lifted along `ULift`), so universe `1` costs nothing here.  No ascent theorem
is used and none is needed.
-/

namespace GroupApproximation
namespace MaximalCStarLiteralBase

open LiteralNonMFPresentation LiteralNonMFEndpoint
open MaximalCStarProperCompression

noncomputable section

/-! ## Property `(T)` for the literal base at the algebra's universe -/

/-- Property `(T)` for the literal twenty-relator affine base at
representation universe `1`, which is the universe the maximal group
C-star algebra of a `Type`-level group lives at.

This is `HasKazhdanPropertyT.liftUniverse`, the direction that holds with no
hypothesis: a representation on a Hilbert space in the smaller universe is
carried along `ULift` into the larger one and the invariant vector comes
back. -/
theorem base_hasKazhdanPropertyT_universeOne :
    HasKazhdanPropertyT.{0, 1} Base :=
  LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT.liftUniverse

/-- The symmetric generating Kazhdan package for the literal base, with the
pair at representation universe `1`.  The tolerance is normalized to at most
`1`, which `StrictKazhdanCompression` asks for and shrinking supplies. -/
theorem exists_pair_package :
    ∃ S : Finset Base, ∃ ε : ℝ, 1 ∈ S ∧ (∀ g ∈ S, g⁻¹ ∈ S) ∧
      Subgroup.closure (S : Set Base) = ⊤ ∧ 0 < ε ∧ ε ≤ 1 ∧
      IsKazhdanPair.{0, 1} Base S ε := by
  obtain ⟨S, hone, hsymm, hgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset Base
      LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT
  obtain ⟨δ, hδ⟩ := KazhdanGenerators.exists_pair_on_generators
    base_hasKazhdanPropertyT_universeOne S hsymm hgen
  have hpos : 0 < min δ 1 := lt_min hδ.1 zero_lt_one
  exact ⟨S, min δ 1, hone, hsymm, hgen, hpos, min_le_right _ _,
    IsKazhdanPair.shrink hδ hpos (min_le_left _ _)⟩

/-! ## Strictness of the literal compression -/

/-- The literal marked word is nontrivial, so the compression is proper. -/
theorem inclusionData_word_ne_one : inclusionData.word ≠ 1 := by
  rw [inclusionData_word]
  exact LiteralNonMFLinearWitness.literal_mark_ne_one

/-- Strictness in mapped-subgroup form: the distinguished base element
escapes the conjugated image, so the inclusion `t ι(Γ) t⁻¹ ⊆ ι(Γ)` is
proper. -/
theorem strictness :
    ∃ a : Base,
      inclusionData.iota a ∉
        (inclusionData.iota.range.map
          (MulAut.conj inclusionData.t).toMonoidHom) := by
  refine ⟨inclusionData.a, fun hmem => ?_⟩
  obtain ⟨x, hx, hconj⟩ := hmem
  obtain ⟨γ, hγ⟩ := hx
  apply inclusionData.iota_a_not_in_compressed_image_of_word_ne_one
    inclusionData_word_ne_one
  exact ⟨γ, by rw [← hconj, ← hγ]; rfl⟩

/-! ## The strict Kazhdan compression of the literal group -/

/-- **The base of `E` is a strict Kazhdan compression inside `E`.**  This is
the aside of the printed remark, as data: the literal group of Definition
`def:E` carries the compression datum the remark quantifies over. -/
theorem nonempty_strictCompression :
    Nonempty (StrictKazhdanCompression Base MarkedGroup) := by
  obtain ⟨S, ε, hone, hsymm, hgen, hpos, hle, hpair⟩ := exists_pair_package
  obtain ⟨a, ha⟩ := strictness
  exact ⟨{ iota := inclusionData.iota
           t := inclusionData.t
           Q := S
           ε := ε
           kazhdan := hpair
           S := S
           QS := Finset.Subset.refl S
           one_mem := hone
           symm := hsymm
           eps_le := hle
           generates := hgen
           compresses := inclusionData.compresses
           strict := ⟨a, ha⟩ }⟩

end

end MaximalCStarLiteralBase
end GroupApproximation
