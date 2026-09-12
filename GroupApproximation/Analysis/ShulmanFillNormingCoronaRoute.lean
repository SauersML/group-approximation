import GroupApproximation.Analysis.MFAlgebraUnitalCoronaEmbedding
import GroupApproximation.Analysis.ShulmanFillConjugatePair
import GroupApproximation.Analysis.ShulmanFillSymmetricDouble
import GroupApproximation.Analysis.ShulmanFillSymmetricDoubleEmbed

/-!
# The conjugate residual of Theorem 16 is Theorem 16

`ShulmanFill.ConjugateWordNormingStatement` of
`Analysis/ShulmanFillConjugatePair` is the bottom of the norming route to
Shulman's Theorem 16: for a word `y` of the amalgam and a `δ > 0` it asks for
discrete models `Z`, a unital compatible pair `(l, r)` into their corona and a
unitary `u` commuting with `l(ι_A C)` whose conjugated pair evaluates `y` to
within `δ` of the amalgam norm.  The docstring of that module calls its step 5
— the conjugated pair reproducing, on a word, the supremum over *all*
compatible pairs that defines the amalgam norm — "of Haagerup--Thorbjørnsen
type and not in the repository", and no published proof of Theorem 16 contains
that estimate.

This module takes the estimate out of the route, by proving the converse of
`shulmanTheorem16_of_conjugateWordNorming`:

`conjugateWordNorming_of_shulmanTheorem16 : ShulmanTheorem16Statement →
ConjugateWordNormingStatement`,

so the two are equivalent (`conjugateWordNorming_iff_shulmanTheorem16`).  The
proof is the degenerate case `u = 1` of the conjugate shape, and nothing in it
is analytic:

1. Theorem 16 makes the amalgam `A₁ *_C A₂` MF.  It is nontrivial, because it
   has a compatible representation with a nontrivial carrier, so
   `MFAlgebraUnitalCoronaEmbedding.exists_injective_unital_coronaEmbedding`
   turns the possibly nonunital MF embedding into a faithful *unital* one
   `e : A₁ *_C A₂ → ∏ M_{Z_n} / ⨁ M_{Z_n}`.
2. Push the two canonical factor maps forward along `e`.  They stay
   compatible (`comp_universalCStarAmalgamLeft_comp_eq`), and the unit
   commutes with the image of `C`, so the conjugate shape is available with no
   unitary left to choose.
3. The evaluation coordinate of that conjugated pair *is* `e`: both are
   `*`-homomorphisms out of the amalgam taking the same values on the two
   factor images, so the uniqueness half of the universal property identifies
   them (`eval_conjugateRepresentation_one_eq`).  An injective
   `*`-homomorphism of C-star algebras is isometric, so the coordinate
   reproduces the amalgam norm exactly, not merely to within `δ`
   (`norm_eval_conjugateRepresentation_one`).

So the conjugate residual is reachable along Shulman's own route, which has no
genericity estimate in it.  Composing with what
`Analysis/ShulmanFillSymmetricDoubleEmbed` and
`Analysis/ShulmanFillSymmetricDouble` already prove,
`conjugateWordNorming_of_symmetricDouble` derives it from Shulman's Theorem 10
(`SymmetricDoubleMFStatement`) and Theorem 13
(`AmalgamEmbedsSymmetricDoubleStatement`).

Theorem 13 is *not* reached from
`ShulmanSymmetricDouble.CompatibleTargetPairStatement` here.  Its reduction in
`Analysis/ShulmanFillSymmetricDoubleEmbedTheorem13` is void: that module's
`symmetricDoubleEmbedding` is ill-typed, because
`MFAlgebraAmalgamCriterion.factorAmalgamToSymmetricTarget` fixes its target in
`Type` while a universal amalgam lives one universe up.  The repair is
`Analysis/ShulmanFillNormingAmalgamWitness`, which routes the same content
through a `Type`-valued target, and this module deliberately does not import
the broken chain.

Nothing here is a new hypothesis: every statement named above is already in
the repository, and this module only proves implications between them.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-! ## Conjugation by the unit

The conjugate shape allows any unitary commuting with the image of the
amalgamated algebra.  The unit is such a unitary and conjugation by it is the
identity, so the shape degenerates to a plain compatible corona pair whenever
one is available. -/

section UnitConjugation

variable {D : Type} [CStarAlgebra D]

/-- Conjugation by the unit is the identity. -/
theorem unitaryConj_one_apply (x : D) :
    unitaryConj (1 : unitary D) x = x := by
  show (1 : D) * x * star (1 : D) = x
  rw [star_one, one_mul, mul_one]

/-- The unit commutes with the image of the amalgamated algebra, in the exact
form `conjugateRepresentation` asks for. -/
theorem one_commutes_amalgamated {C A : Type} [CStarAlgebra C] [CStarAlgebra A]
    (iA : C →⋆ₐ[ℂ] A) (l : A →⋆ₐ[ℂ] D) :
    ∀ c : C, ((1 : unitary D) : D) * l (iA c) =
      l (iA c) * ((1 : unitary D) : D) := by
  intro c
  show (1 : D) * l (iA c) = l (iA c) * (1 : D)
  rw [one_mul, mul_one]

end UnitConjugation

/-! ## Pushing the canonical factor maps forward -/

section Amalgam

variable {C A B : Type} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
  (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
  [Nonempty (CStarAmalgamRepresentation iA iB)]

/-- The universal amalgam of a datum with at least one compatible
representation is nontrivial: an evaluation coordinate carries `1` to `1` and
`0` to `0`, and its carrier is nontrivial by definition. -/
theorem nontrivial_universalCStarAmalgam :
    Nontrivial (UniversalCStarAmalgam iA iB) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro hone
  have R : CStarAmalgamRepresentation iA iB := Classical.arbitrary _
  have h := congrArg (universalCStarAmalgamEval iA iB R) hone
  rw [map_one, map_zero] at h
  exact one_ne_zero h

/-- **Pushing the two canonical factor maps forward keeps them compatible.**
The canonical maps agree on `C` inside the amalgam, so their composites with
any homomorphism out of the amalgam agree on `C` too. -/
theorem comp_universalCStarAmalgamLeft_comp_eq {E : Type} [CStarAlgebra E]
    (e : UniversalCStarAmalgam iA iB →⋆ₐ[ℂ] E) :
    (e.comp (universalCStarAmalgamLeft iA iB)).comp iA =
      (e.comp (universalCStarAmalgamRight iA iB)).comp iB := by
  apply StarAlgHom.ext
  intro c
  exact congrArg e
    (DFunLike.congr_fun (universalCStarAmalgam_compatible iA iB) c)

/-- **A compatible pair that `e` realizes is evaluated by `e`.**  If a
compatible pair `(l, r)` is the pushforward of the two canonical factor maps
along a homomorphism `e` out of the amalgam, then the evaluation coordinate of
the pair conjugated by the unit is `e` itself: both are `*`-homomorphisms out
of the amalgam taking the same values on the two factor images, so the
uniqueness half of `universalCStarAmalgam_existsUnique_lift` identifies
them. -/
theorem eval_conjugateRepresentation_one_eq {E : Type} [CStarAlgebra E]
    [Nontrivial E] (e : UniversalCStarAmalgam iA iB →⋆ₐ[ℂ] E)
    (l : A →⋆ₐ[ℂ] E) (r : B →⋆ₐ[ℂ] E) (hlr : l.comp iA = r.comp iB)
    (hu : ∀ c : C, ((1 : unitary E) : E) * l (iA c) =
      l (iA c) * ((1 : unitary E) : E))
    (hleft : ∀ a : A, e (universalCStarAmalgamLeft iA iB a) = l a)
    (hright : ∀ b : B, e (universalCStarAmalgamRight iA iB b) = r b) :
    universalCStarAmalgamEval iA iB
        (conjugateRepresentation iA iB l r hlr 1 hu) = e := by
  obtain ⟨f, _hf, huniq⟩ :=
    universalCStarAmalgam_existsUnique_lift iA iB l
      ((unitaryConj (1 : unitary E)).comp r)
      (unitaryConj_comp_compatible iA iB l r hlr 1 hu)
  refine (huniq (universalCStarAmalgamEval iA iB
      (conjugateRepresentation iA iB l r hlr 1 hu))
    ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩).trans (huniq e ⟨hleft, ?_⟩).symm
  intro b
  show e (universalCStarAmalgamRight iA iB b) =
    unitaryConj (1 : unitary E) (r b)
  rw [unitaryConj_one_apply]
  exact hright b

/-- **A faithful embedding of the amalgam gives the conjugate shape on the
nose.**  With the unit as conjugating unitary the evaluation coordinate of the
pair is the embedding itself, and an injective `*`-homomorphism of C-star
algebras is isometric, so the coordinate reproduces the amalgam norm exactly
rather than to within an error. -/
theorem norm_eval_conjugateRepresentation_one {E : Type} [CStarAlgebra E]
    [Nontrivial E] (e : UniversalCStarAmalgam iA iB →⋆ₐ[ℂ] E)
    (he : Function.Injective e)
    (l : A →⋆ₐ[ℂ] E) (r : B →⋆ₐ[ℂ] E) (hlr : l.comp iA = r.comp iB)
    (hu : ∀ c : C, ((1 : unitary E) : E) * l (iA c) =
      l (iA c) * ((1 : unitary E) : E))
    (hleft : ∀ a : A, e (universalCStarAmalgamLeft iA iB a) = l a)
    (hright : ∀ b : B, e (universalCStarAmalgamRight iA iB b) = r b)
    (x : UniversalCStarAmalgam iA iB) :
    ‖universalCStarAmalgamEval iA iB
        (conjugateRepresentation iA iB l r hlr 1 hu) x‖ = ‖x‖ := by
  rw [eval_conjugateRepresentation_one_eq iA iB e l r hlr hu hleft hright]
  have hiso : Isometry e :=
    NonUnitalStarAlgHom.isometry e.toNonUnitalStarAlgHom he
  exact hiso.norm_map_of_map_zero (map_zero _) x

end Amalgam

/-! ## The residual, from Theorem 16 -/

/-- **The conjugate residual of Theorem 16 follows from Theorem 16 itself.**
Theorem 16 makes the amalgam MF; a nontrivial MF algebra has a faithful
*unital* norm-matrix-corona embedding, and pushing the two canonical factor
maps forward along it gives a unital compatible corona pair whose evaluation
coordinate is that embedding.  The unit is a legitimate conjugating unitary,
and the coordinate is isometric, so the required inequality holds with room to
spare.

With `shulmanTheorem16_of_conjugateWordNorming` of
`Analysis/ShulmanFillConjugatePair` this makes the two statements equivalent:
the norming route loses nothing, and its step 5 is not a harder statement than
the theorem it was introduced to prove. -/
theorem conjugateWordNorming_of_shulmanTheorem16
    (h16 : Manuscript.MFRecognition.HNNPermanence.ShulmanTheorem16Statement) :
    ConjugateWordNormingStatement := by
  intro C A₁ A₂ _ _ _ iA iB _ hC hA₁ hA₂ Y _ phiA phiB hphiA hphiB hcomp
    y _hy δ hδ
  have hMF : IsMFAlgebra (UniversalCStarAmalgam iA iB) :=
    h16 iA iB hC hA₁ hA₂ Y phiA phiB hphiA hphiB hcomp
  haveI : Nontrivial (UniversalCStarAmalgam iA iB) :=
    nontrivial_universalCStarAmalgam iA iB
  obtain ⟨Z, hZ, e, he⟩ :=
    MFAlgebraUnitalCoronaEmbedding.exists_injective_unital_coronaEmbedding hMF
  letI : ∀ n, Nonempty (Z n) := hZ
  have hfinal : ‖y‖ - δ ≤ ‖universalCStarAmalgamEval iA iB
      (conjugateRepresentation iA iB
        (e.comp (universalCStarAmalgamLeft iA iB))
        (e.comp (universalCStarAmalgamRight iA iB))
        (comp_universalCStarAmalgamLeft_comp_eq iA iB e) 1
        (one_commutes_amalgamated iA
          (e.comp (universalCStarAmalgamLeft iA iB)))) y‖ := by
    rw [norm_eval_conjugateRepresentation_one iA iB e he
      (e.comp (universalCStarAmalgamLeft iA iB))
      (e.comp (universalCStarAmalgamRight iA iB))
      (comp_universalCStarAmalgamLeft_comp_eq iA iB e)
      (one_commutes_amalgamated iA (e.comp (universalCStarAmalgamLeft iA iB)))
      (fun _ ↦ rfl) (fun _ ↦ rfl) y]
    linarith
  exact ⟨Z, hZ, e.comp (universalCStarAmalgamLeft iA iB),
    e.comp (universalCStarAmalgamRight iA iB),
    comp_universalCStarAmalgamLeft_comp_eq iA iB e, 1,
    one_commutes_amalgamated iA (e.comp (universalCStarAmalgamLeft iA iB)),
    hfinal⟩

/-- **The conjugate residual and Shulman's Theorem 16 are the same
statement.**  The forward direction is the reduction chain
`ShulmanFillTheorem16 → ShulmanFillDenseNorming → ShulmanFillWordNorming →
ShulmanFillConjugatePair`; the backward direction is the theorem above. -/
theorem conjugateWordNorming_iff_shulmanTheorem16 :
    ConjugateWordNormingStatement ↔
      Manuscript.MFRecognition.HNNPermanence.ShulmanTheorem16Statement :=
  ⟨shulmanTheorem16_of_conjugateWordNorming,
    conjugateWordNorming_of_shulmanTheorem16⟩

/-! ## The residual on Shulman's own route -/

/-- **The conjugate residual from Shulman's Theorems 10 and 13.**  No
genericity estimate enters: `ShulmanFillSymmetricDoubleEmbed` assembles the
printed criterion from those two — unitalizing the corona pair on its common
support corner and taking `D` to be the corona algebra generated by the two
unital images — and the equivalence above carries it back to the conjugate
shape. -/
theorem conjugateWordNorming_of_symmetricDouble
    (hDouble : ShulmanSymmetricDouble.SymmetricDoubleMFStatement)
    (hEmbed : ShulmanSymmetricDouble.AmalgamEmbedsSymmetricDoubleStatement) :
    ConjugateWordNormingStatement :=
  conjugateWordNorming_of_shulmanTheorem16
    (ShulmanSymmetricDouble.shulmanTheorem16_of_symmetricDouble hDouble hEmbed)

end

end ShulmanFill
end GroupApproximation
