import GroupApproximation.Sofic.BareDefectSource
import GroupApproximation.Sofic.FournierFacioUniversalGroup
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Algebra.HNNFinitePresentation

/-!
# The compression source over `KC.21`

`BareDefectSourceData P E` (`Sofic/BareDefectSource.lean`) is what the
non-MF endpoint consumes: a property-`(T)` base `P`, an ambient group `E`
compressing it by a stable letter, a protected element centralized by the
compressed copy, and one nontrivial marked commutator.  The file that
defines it records the irreducible obligation — *the base must be an
infinite property-`(T)` group carrying a strictly proper self-compression*
— and rules out the one explicit source the repository had, because its
base is `ℤ`.

This module discharges that obligation from `KC.21`.  A
`UniversalKazhdanGroup` is finitely presented, torsion-free, Kazhdan and
contains a copy of every finitely presented torsion-free group; applying
universality to `P × P` gives an embedding `j : P × P ↪ P`, and
`α := j(·, 1)` is a proper self-embedding of a Kazhdan group.  Feeding `α`
to the repository's affine HNN skeleton produces the source.

## What this costs: nothing new

Every step is an in-repo lemma applied at a new group.  The pieces, in the
order they are used:

* `ProductFinitePresentation.instProd` and `IsPowerTorsionFree.prod` make
  `P × P` finitely presented and torsion-free, so universality applies —
  this is exactly `FournierFacioUniversal.nonempty_containsSquare`, which
  already packages `j` as a `ContainsSquare`;
* `ContainsSquare.alpha`, `.alpha_injective` and
  `.emb_inr_not_mem_range_alpha` supply `α`, its injectivity, and an
  element outside its image, the last needing only `b ≠ 1`;
* `FournierFacioUniversal.exists_ne_one_of_universal` supplies that `b`;
* `ConcreteCompressionSource.sourceData` turns any injective endomorphism
  with an element outside its image into a `CompressionSourceData`,
  Britton's lemma included;
* `CompressionSourceData.toBareDefectSourceData` adds the one missing
  field, property `(T)`, which is `KC.21`'s own.

So there is no new mathematics here and no open leaf: the module is an
application, and every clause of `BareDefectSourceData` is proved.

## Two simplifications against the design note

`notes/KAZHDAN_ENVELOPE_BESPOKE_ROUTE_2026-08-22.md` §1 sketches this
construction with `s := j(1, x)` as the protected element, and argues that
such an `x` can be chosen non-central because universality embeds a
nonabelian free group into `P`.  Neither the choice nor the argument is
needed.

*The protected element.*  The repository's affine skeleton does not
protect an element of `P` at all.  Its base is `P × Multiplicative ℤ` and
its protected element is the transported generator of the central cyclic
direction, so `commutesAfterCompression` is centrality in the base
(`ConcreteCompressionSource.commute_tct_compressed`) rather than a fact
about `j`, and the marked commutator is nontrivial by Britton's lemma
(`commutator_tct_ne_one`).

*The properness argument.*  What the skeleton asks of `α` is one element
outside its image, and `j(1, b) ∈ Set.range α` would force `(1, b) = (g, 1)`
by injectivity of `j`, hence `b = 1`.  So `b ≠ 1` is the whole hypothesis:
no free subgroup, no centrality, no nonabelian input.  `F₂ ↪ P` is
available (`FournierFacioUniversal.containsEveryFiniteRankFreeGroup`) and
is not used.

## The envelope's own permanence

`BareDefectSourceData` demands nothing of `E`, but the routing stage
downstream does, so the two standard permanence facts are recorded here
at this envelope: `envelope_isPowerTorsionFree` from
`HNNBritton.isPowerTorsionFree_sourceGroup`, and
`envelope_isFinitelyPresented` from
`HNNFinitePresentation.isFinitelyPresented_hnnExtension`.  Both are
corollaries, not obligations of the source interface.
-/

namespace GroupApproximation
namespace SourceFromUniversalKazhdan

open RealizationFromUniversalGroup

/-! ## The envelope of a self-square -/

section Square

variable {P : Type} [Group P] (h : ContainsSquare P)

/-- **The compression envelope.**  The affine HNN skeleton of
`α = j(·, 1)`: the base is `P × Multiplicative ℤ` and the stable letter
conjugates the base copy of `P` onto the base copy of its `α`-image. -/
noncomputable abbrev Envelope : Type :=
  ConcreteCompressionSource.SourceGroup h.alpha h.alpha_injective

/-- **The compression source of a self-square.**  Any nontrivial `b` makes
`α` proper, because `j(1, b)` lies outside its image, and properness is
the only hypothesis the affine skeleton needs. -/
noncomputable def compressionSourceData {b : P} (hb : b ≠ 1) :
    ConcreteCompressionSource.CompressionSourceData P (Envelope h) :=
  ConcreteCompressionSource.sourceData h.alpha h.alpha_injective
    (h.emb_inr_not_mem_range_alpha hb)

/-- **The slimmed defect source over a Kazhdan self-square.**  Property
`(T)` of the base is the one field the compression skeleton does not
already carry, so supplying it completes the datum. -/
noncomputable def bareDefectSourceData {b : P} (hb : b ≠ 1)
    (hT : HasKazhdanPropertyT.{0, 0} P) : BareDefectSourceData P (Envelope h) :=
  (compressionSourceData h hb).toBareDefectSourceData hT

/-- The witness of the source is the second-factor element that certifies
properness. -/
@[simp] theorem bareDefectSourceData_witness {b : P} (hb : b ≠ 1)
    (hT : HasKazhdanPropertyT.{0, 0} P) :
    (bareDefectSourceData h hb hT).witness = h.emb (1, b) := rfl

/-- The compression of the source is conjugation by the stable letter. -/
@[simp] theorem bareDefectSourceData_u {b : P} (hb : b ≠ 1)
    (hT : HasKazhdanPropertyT.{0, 0} P) :
    (bareDefectSourceData h hb hT).u = HNNExtension.t := rfl

/-! ## Permanence for the envelope

Neither fact is a field of `BareDefectSourceData`; both are what the
routing stage asks of `E`. -/

/-- The envelope is torsion-free whenever the base is, by the HNN torsion
theorem cashed at this very skeleton. -/
theorem envelope_isPowerTorsionFree (htf : IsPowerTorsionFree P) :
    IsPowerTorsionFree (Envelope h) :=
  HNNBritton.isPowerTorsionFree_sourceGroup h.alpha h.alpha_injective
    (htf.prod ConcreteCompressionSource.isPowerTorsionFree_multiplicative_int)

/-- The envelope is finitely presented whenever the base is: the HNN base
`P × Multiplicative ℤ` is finitely presented by the direct-product
theorem, and the unmoved associated subgroup is the range of a
homomorphism out of a finitely generated group. -/
theorem envelope_isFinitelyPresented [Group.IsFinitelyPresented P] :
    Group.IsFinitelyPresented (Envelope h) := by
  letI : Group.FG P := ProductFinitePresentation.fg_of_isFinitelyPresented P
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension
    (ConcreteCompressionSource.sourceEquiv h.alpha h.alpha_injective)

end Square

/-! ## The source over `KC.21` -/

section Universal

variable (U : FournierFacioUniversal.UniversalKazhdanGroup)

/-- The self-square of `KC.21`, chosen once. -/
noncomputable def square : ContainsSquare U.Carrier :=
  Classical.choice (FournierFacioUniversal.nonempty_containsSquare U)

/-- A nontrivial element of `KC.21`, chosen once.  It exists because
`Multiplicative ℤ` is finitely presented and torsion-free, so universality
embeds it.  It is what makes the self-embedding `α` strictly proper, and
nothing else is asked of it. -/
noncomputable def nontrivialElement : U.Carrier :=
  Classical.choose (FournierFacioUniversal.exists_ne_one_of_universal U.universal)

theorem nontrivialElement_ne_one : nontrivialElement U ≠ 1 :=
  Classical.choose_spec (FournierFacioUniversal.exists_ne_one_of_universal U.universal)

/-- **The compression envelope over `KC.21`.** -/
noncomputable abbrev UniversalEnvelope : Type := Envelope (square U)

/-- **The slimmed defect source over `KC.21`, with every clause proved.**
The base is `KC.21` itself, so `kazhdan` is its own field; the ambient
group is the affine HNN skeleton of `j(·, 1)`. -/
noncomputable def universalBareDefectSourceData :
    BareDefectSourceData U.Carrier (UniversalEnvelope U) :=
  bareDefectSourceData (square U) (nontrivialElement_ne_one U) U.kazhdan

/-- The envelope over `KC.21` is torsion-free. -/
theorem universalEnvelope_isPowerTorsionFree :
    IsPowerTorsionFree (UniversalEnvelope U) :=
  envelope_isPowerTorsionFree (square U) U.torsionFree

/-- The envelope over `KC.21` is finitely presented. -/
theorem universalEnvelope_isFinitelyPresented :
    Group.IsFinitelyPresented (UniversalEnvelope U) :=
  envelope_isFinitelyPresented (square U)

/-- The base of the source is infinite, as the slimmed interface requires.
Derived, not assumed: the compression is injective and strictly proper. -/
theorem universal_infinite_base : Infinite U.Carrier :=
  (universalBareDefectSourceData U).infinite_source

/-- The compression over `KC.21` is strictly proper. -/
theorem universal_not_conjugation_surjective :
    ¬ ∀ p : U.Carrier, ∃ q : U.Carrier,
      (universalBareDefectSourceData U).u *
        (universalBareDefectSourceData U).iota q *
        (universalBareDefectSourceData U).u⁻¹ =
        (universalBareDefectSourceData U).iota p :=
  (universalBareDefectSourceData U).not_conjugation_surjective

/-- **`KC.21` inhabits the slimmed source interface.**  The `Nonempty`
form, with the envelope's two permanence facts alongside. -/
theorem exists_bareDefectSourceData_of_universalKazhdan :
    ∃ (E : Type) (_ : Group E) (_ : BareDefectSourceData U.Carrier E),
      IsPowerTorsionFree E ∧ Group.IsFinitelyPresented E :=
  ⟨UniversalEnvelope U, inferInstance, universalBareDefectSourceData U,
    universalEnvelope_isPowerTorsionFree U,
    universalEnvelope_isFinitelyPresented U⟩

/-- **The packaged deliverable.**  A `UniversalKazhdanGroup` yields a base,
an ambient group, and a slimmed defect source over them. -/
noncomputable def bareDefectSourceData_of_universalKazhdan :
    Σ' (P E : Type) (_ : Group P) (_ : Group E), BareDefectSourceData P E :=
  ⟨U.Carrier, UniversalEnvelope U, inferInstance, inferInstance,
    universalBareDefectSourceData U⟩

end Universal

end SourceFromUniversalKazhdan
end GroupApproximation
