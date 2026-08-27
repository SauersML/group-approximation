import GroupApproximation.Kazhdan.KazhdanFiniteIndex
import GroupApproximation.Monsters.SL3ElementaryGeneration
import GroupApproximation.Sofic.LiteralP13HodgeCertificate

/-!
# Property `(T)` for `SL₃(ℤ)` and its finite-index subgroups

The exact rational Hodge certificate of `Sofic/LiteralP13HodgeCertificate.lean`
is stated for the abstract thirteen-relator presentation `P13`, not for a matrix
group.  This module cashes it in on the actual special linear group.

## The route

Nothing analytic happens here.  The three inputs are already theorems:

* the certificate itself — `LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT`,
  an exact finite rational sum-of-squares decomposition
  `Δ₁ = (1/250)·I + Q⁺Q + R` with `ℓ1` residual bound `1/500`, replayed through
  `ExactHodgeCertificate.Certificate.hasKazhdanPropertyT`;
* the presentation map `toSL3 : P13 →* SL₃(ℤ)` of
  `Monsters/LiteralP13MatrixModel.lean`, which exists because each of the
  thirteen relators is a closed identity of `3 × 3` integer matrices;
* its surjectivity `SL3ElementaryGeneration.toSL3_surjective`, which is the
  classical Euclidean reduction: elementary generation of `SL₃(ℤ)`.

Property `(T)` passes to quotients (`HasKazhdanPropertyT.of_surjective`), so the
composite is immediate.  In particular **no new certificate data is needed for
`SL₃(ℤ)`**: `P13` is the Steinberg-type presentation whose generators are the
six elementary transvections, and the certificate was computed there.

Note that only *surjectivity* of `toSL3` is used.  Injectivity — completeness of
the presentation, classically the unstable computation `K₂(3,ℤ) = ℤ/2` — is a
strictly deeper statement and is not assumed anywhere below.

## Finite-index subgroups

`hasKazhdanPropertyT_of_finiteIndex_in_sl3` transports the conclusion to every
finite-index subgroup, via `FiniteIndex.hasKazhdanPropertyT_of_finiteIndex`
(Bekka--de la Harpe--Valette, Theorem 1.7.1, proved in
`Kazhdan/KazhdanFiniteIndex.lean`).  It is stated for an arbitrary finite-index
subgroup rather than for a particular congruence subgroup deliberately: the
principal congruence subgroup `Γ(3)` is defined by the partner-group interface,
and duplicating that definition here would leave two `Γ(3)`s in the tree.

Torsion-freeness (Minkowski) and finite presentation of `Γ(3)` are *not*
addressed here and are not assumed here.

## Universes

`HasKazhdanPropertyT.{0, w}` throughout, matching
`LiteralP13HodgeCertificate.p13_hasKazhdanPropertyTReal` and the shape
`hasKazhdanPropertyT_of_finiteIndex` consumes.  Both groups live in `Type 0`, so
the universe of the representation spaces is the only free level, and it is
raised by `HasKazhdanPropertyT.liftUniverse` rather than assumed.
-/

namespace GroupApproximation
namespace SL3Certificate

universe w

open LiteralP13MatrixModel LiteralP13Presentation

/-! ## The generating tuple

The certificate's six generators, read on matrices.  These identities are
definitional; they are displayed so that a later edit of `elem` cannot silently
change which group the certificate is about. -/

/-- The six elementary matrices carrying the certificate, in the exact
certificate order `e₁₂, e₁₃, e₂₁, e₂₃, e₃₁, e₃₂`. -/
structure ElementaryGenerators : Prop where
  elem_0 : (elem 0 : Matrix (Fin 3) (Fin 3) ℤ) = !![1, 1, 0; 0, 1, 0; 0, 0, 1]
  elem_1 : (elem 1 : Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 1; 0, 1, 0; 0, 0, 1]
  elem_2 : (elem 2 : Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 0; 1, 1, 0; 0, 0, 1]
  elem_3 : (elem 3 : Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 0; 0, 1, 1; 0, 0, 1]
  elem_4 : (elem 4 : Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 0; 0, 1, 0; 1, 0, 1]
  elem_5 : (elem 5 : Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 0; 0, 1, 0; 0, 1, 1]
  generates : Subgroup.closure (Set.range elem) = ⊤
  image_of_certificate_generators : ∀ i, toSL3 (p13Generator i) = elem i

theorem elementaryGenerators : ElementaryGenerators where
  elem_0 := rfl
  elem_1 := rfl
  elem_2 := rfl
  elem_3 := rfl
  elem_4 := rfl
  elem_5 := rfl
  generates := SL3ElementaryGeneration.closure_range_elem_eq_top
  image_of_certificate_generators := toSL3_of

/-! ## Property `(T)` for `SL₃(ℤ)` -/

/-- **`SL₃(ℤ)` has Kazhdan's property `(T)`.**

The exact rational Hodge certificate for the thirteen-relator Steinberg
presentation, pushed forward along the surjection onto the matrix group.  No
mathematical premise beyond the finite rational identities of the certificate,
the thirteen kernel-checked matrix relator identities, and Euclidean reduction
in `SL₃(ℤ)`. -/
theorem sl3_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (Matrix.SpecialLinearGroup (Fin 3) ℤ) :=
  HasKazhdanPropertyT.of_surjective toSL3 SL3ElementaryGeneration.toSL3_surjective
    LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT

/-- Property `(T)` for `SL₃(ℤ)` at an arbitrary representation universe. -/
theorem sl3_hasKazhdanPropertyTReal :
    HasKazhdanPropertyT.{0, w} (Matrix.SpecialLinearGroup (Fin 3) ℤ) :=
  sl3_hasKazhdanPropertyT.liftUniverse

/-! ## Finite-index subgroups

Every finite-index subgroup of `SL₃(ℤ)` inherits property `(T)`.  The principal
congruence subgroup `Γ(3) = ker (SL₃(ℤ) → SL₃(ℤ/3))` is the intended instance;
it is supplied by the partner-group interface rather than redefined here. -/

/-- **Property `(T)` for every finite-index subgroup of `SL₃(ℤ)`.**  Applied to
the principal congruence subgroup `Γ(3)`, this is the Kazhdan half of the
torsion-free finitely presented partner group. -/
theorem hasKazhdanPropertyT_of_finiteIndex_in_sl3
    (Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) [Λ.FiniteIndex] :
    HasKazhdanPropertyT.{0, 0} ↥Λ :=
  GroupApproximation.FiniteIndex.hasKazhdanPropertyT_of_finiteIndex Λ
    sl3_hasKazhdanPropertyT

/-- The same conclusion at an arbitrary representation universe. -/
theorem hasKazhdanPropertyT_of_finiteIndex_in_sl3Real
    (Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) [Λ.FiniteIndex] :
    HasKazhdanPropertyT.{0, w} ↥Λ :=
  (hasKazhdanPropertyT_of_finiteIndex_in_sl3 Λ).liftUniverse

end SL3Certificate
end GroupApproximation
