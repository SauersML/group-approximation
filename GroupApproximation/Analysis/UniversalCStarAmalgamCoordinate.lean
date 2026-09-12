import GroupApproximation.Analysis.UniversalCStarAmalgam
import GroupApproximation.Analysis.UniversalCStarHNN

/-!
# Coordinate evaluation is reading an ambient coordinate

Both universal objects of this development are closed star subalgebras of a
bounded product indexed by their own representation family, and both carry an
evaluation homomorphism at one coordinate.  That evaluation is built as the
composite of the subalgebra inclusion with reading the coordinate off the
ambient family, so the two spellings are definitionally equal and the
identities below are `rfl`.

Naming them matters where a coordinate goal has been reached by `lp.ext` and
`funext`.  The ambient side of such a goal is written with
`StarSubalgebra.subtype`, while every lemma about a coordinate -- the two
factor-image lemmas for the amalgam, the base and stable lemmas for the HNN
algebra, and corner functoriality along an evaluation -- is written with the
evaluation.  Rewriting with `subtype_apply_eq_universalCStarAmalgamEval` or
its HNN twin puts the goal back into the vocabulary that has the API, which
replaces one deep definitional check by a rewrite the existing simp set can
finish.

Only that direction is a `simp` lemma.  The reverse direction matches *every*
coordinate evaluation, so as a `simp` lemma it would fire ahead of
`universalCStarAmalgamEval_left`, `universalCStarHNNEval_base` and their
siblings and rewrite goals out of the vocabulary those lemmas need.
-/

namespace GroupApproximation

open scoped CStarAlgebra ENNReal

noncomputable section

universe u

/-! ## The full amalgam -/

/-- Evaluating an element of the universal amalgam at a compatible coordinate
reads that coordinate of its ambient bounded family.

Deliberately not a `simp` lemma: its left-hand side matches every coordinate
evaluation.  Use `subtype_apply_eq_universalCStarAmalgamEval` for the
rewriting direction. -/
theorem universalCStarAmalgamEval_eq_subtype_apply
    {C A B : Type u} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (Q : CStarAmalgamRepresentation iA iB) (p : UniversalCStarAmalgam iA iB) :
    universalCStarAmalgamEval iA iB Q p =
      (universalCStarAmalgamSubalgebra iA iB).subtype p Q :=
  rfl

/-- Reading a coordinate of the ambient family of an element of the universal
amalgam is evaluating it at that coordinate.  This is the direction a
coordinate goal needs after `lp.ext`. -/
@[simp] theorem subtype_apply_eq_universalCStarAmalgamEval
    {C A B : Type u} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (Q : CStarAmalgamRepresentation iA iB) (p : UniversalCStarAmalgam iA iB) :
    (universalCStarAmalgamSubalgebra iA iB).subtype p Q =
      universalCStarAmalgamEval iA iB Q p :=
  rfl

/-! ## The universal HNN algebra -/

/-- Evaluating an element of the universal HNN algebra at a covariant
coordinate reads that coordinate of its ambient bounded family.

Deliberately not a `simp` lemma, for the reason recorded on the amalgam
version. -/
theorem universalCStarHNNEval_eq_subtype_apply
    {D : Type u} [CStarAlgebra D] (B0 B1 : StarSubalgebra ℂ D)
    (theta : B0 ≃⋆ₐ[ℂ] B1)
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    (R : CStarHNNRepresentation B0 B1 theta)
    (x : UniversalCStarHNN B0 B1 theta) :
    universalCStarHNNEval B0 B1 theta R x =
      (universalCStarHNNSubalgebra B0 B1 theta).subtype x R :=
  rfl

/-- Reading a coordinate of the ambient family of an element of the universal
HNN algebra is evaluating it at that coordinate. -/
@[simp] theorem subtype_apply_eq_universalCStarHNNEval
    {D : Type u} [CStarAlgebra D] (B0 B1 : StarSubalgebra ℂ D)
    (theta : B0 ≃⋆ₐ[ℂ] B1)
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    (R : CStarHNNRepresentation B0 B1 theta)
    (x : UniversalCStarHNN B0 B1 theta) :
    (universalCStarHNNSubalgebra B0 B1 theta).subtype x R =
      universalCStarHNNEval B0 B1 theta R x :=
  rfl

end

end GroupApproximation
