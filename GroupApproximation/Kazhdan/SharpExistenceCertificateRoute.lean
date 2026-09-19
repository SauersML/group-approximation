import GroupApproximation.Kazhdan.ExactHodgeCertificate
import GroupApproximation.Kazhdan.TorsionFreeHyperbolicKazhdan

/-!
# `SharpExistence` from a finite rational certificate

This module connects two things that were already in the repository and had
never been wired together: the endpoint `SharpExistence`, and the exact Hodge
certificate machine of `Kazhdan/ExactHodgeCertificate.lean`.

`ExactHodgeCertificate.Certificate.hasKazhdanPropertyT` is **group-agnostic**.
Given any group `G`, any finite generating tuple `s : I → G`, and a
`Certificate (generatorCoboundary s) B q R c r` --- finite rational data in
`ℚ[G]`: a Gram decomposition of the degree-one Hodge matrix as
`c·1 + (sum of squares) + R` with the residual `R` controlled in coefficient
`ℓ¹` by some `r < c` --- it returns `HasKazhdanPropertyT`, with no mathematical
premise beyond those identities and inequalities.  That is the Ozawa /
Netzer--Thom positivity route to property `(T)`, the one Kaluba, Nowak and
Ozawa used for `SL₃(ℤ)` and `Aut(F₅)`.

`sharpExistence_of_hodgeCertificate` below is the consequence: **every analytic
ingredient of `SharpExistence` is already discharged in this repository.**  What
remains is not a theorem to prove but an object to exhibit.

## What the theorem says is left

Exactly this: a group `G` that is

* infinite, finitely presented and torsion-free --- all three cheap for concrete
  presentations;
* hyperbolic in the four-point sense of `Algebra/HyperbolicGroup.lean`;
* equipped with a finite rational Hodge certificate for one finite generating
  tuple.

The last item is a *computation* --- a semidefinite solve followed by rational
rounding --- not a formalization of a deep theorem.  The hyperbolicity clause is
the one that is still mathematics: the library currently exhibits only finite
groups, the trivial group and `Multiplicative ℤ` as hyperbolic.

## Why this route is different from the other three

`Kazhdan/SharpExistenceRoutes.lean` proves that the random-group route's input
is *equivalent* to `SharpExistence`, and `Kazhdan/SharpExistenceSpectralRoute.lean`
proves the same of the spectral route.  Both are therefore citations rather than
reductions.

No converse is proved here, and that is not an oversight: the converse is
Ozawa's theorem that a group with property `(T)` admits such a certificate, which
is not formalized anywhere in this repository.  So this is the first route to
`SharpExistence` recorded here whose input is not known to be equivalent to its
conclusion --- it is a genuine reduction, to finite rational data.

## The honest caveat

Every published certificate of this kind is for a group that is **not**
hyperbolic: `SL₃(ℤ)`, `SL₄(ℤ)`, `Aut(F₅)` and their relatives all contain `ℤ²`,
which no hyperbolic group does.  The known hyperbolic Kazhdan groups are the
cocompact lattices in `Sp(n,1)` and the Ballmann--Świątkowski/Żuk complexes, and
for those the certificate has to be produced rather than cited.  Nothing below
produces one, and `SharpExistence` is not proved here, not assumed here, and no
declaration below is conditional on it.
-/

namespace GroupApproximation

namespace ExactHodgeCertificate

/-! ## A finite presentation needs only its rational certificate -/

/-- **A finite presented-group certificate gives a Kazhdan group directly.**

For a finite generator alphabet and a finite relator list, finite presentation
is an instance and the canonical generators generate by
`PresentedGroup.closure_range_of`. Thus an explicit rational Hodge certificate
is the only input needed here: neither a generating proof nor an abstract
group-level property `(T)` premise is exposed to the caller.

This is the concrete handoff for a future triangular/link computation. Such a
computation may name its finite relators and fill the coefficient identities
in `Certificate`; this theorem turns those checked identities into the exact
property `(T)` consumed by the hyperbolic-partner construction. -/
theorem finitePresentation_kazhdan_of_hodgeCertificate
    {α J K : Type} [Fintype α] [DecidableEq α] [Fintype J] [Fintype K]
    (hα : Nonempty α) (relators : Finset (FreeGroup α))
    {B : J → α → RatGroupRing
      (PresentedGroup (relators : Set (FreeGroup α)))}
    {q : K → α → RatGroupRing
      (PresentedGroup (relators : Set (FreeGroup α)))}
    {R : α → α → RatGroupRing
      (PresentedGroup (relators : Set (FreeGroup α)))}
    {c r : ℚ}
    (C : Certificate
      (generatorCoboundary
        (PresentedGroup.of :
          α → PresentedGroup (relators : Set (FreeGroup α))))
      B q R c r) :
    Group.IsFinitelyPresented
        (PresentedGroup (relators : Set (FreeGroup α))) ∧
      HasKazhdanPropertyT.{0, 0}
        (PresentedGroup (relators : Set (FreeGroup α))) := by
  refine ⟨inferInstance, Certificate.hasKazhdanPropertyT hα
    (PresentedGroup.of :
      α → PresentedGroup (relators : Set (FreeGroup α))) ?_ C⟩
  exact PresentedGroup.closure_range_of (relators : Set (FreeGroup α))

end ExactHodgeCertificate

namespace Hyperbolic

/-! ## The reduction -/

/-- **`SharpExistence` from a finite rational Hodge certificate.**

Every clause but the certificate is a property of a concrete presentation; the
property `(T)` clause is discharged by
`ExactHodgeCertificate.Certificate.hasKazhdanPropertyT`, which is proved in this
repository and takes no analytic input.  So this theorem has no mathematical
hypothesis at all beyond the data it is handed. -/
theorem sharpExistence_of_hodgeCertificate
    {G : Type} [inst : Group G] [Group.IsFinitelyPresented G] [Infinite G]
    (htf : IsPowerTorsionFree G) (hhyp : IsHyperbolicGroup G)
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    (hI : Nonempty I) (s : I → G)
    (hgen : Subgroup.closure (Set.range s) = ⊤)
    {B : J → I → ExactHodgeCertificate.RatGroupRing G}
    {q : K → I → ExactHodgeCertificate.RatGroupRing G}
    {R : I → I → ExactHodgeCertificate.RatGroupRing G} {c r : ℚ}
    (C : ExactHodgeCertificate.Certificate
      (ExactHodgeCertificate.generatorCoboundary s) B q R c r) :
    SharpExistence :=
  ⟨G, inst, inferInstance, inferInstance, htf, hhyp,
    ExactHodgeCertificate.Certificate.hasKazhdanPropertyT hI s hgen C⟩

/-- The same statement with the group's four cheap clauses gathered, so that a
prospective witness can be read off as a checklist: supply a finitely presented
infinite torsion-free group, prove it hyperbolic, and hand over a certificate. -/
theorem sharpExistence_of_hodgeCertificate'
    {G : Type} [inst : Group G] [Group.IsFinitelyPresented G] [Infinite G]
    (hcheap : IsPowerTorsionFree G ∧ IsHyperbolicGroup G)
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    (hI : Nonempty I) (s : I → G)
    (hgen : Subgroup.closure (Set.range s) = ⊤)
    {B : J → I → ExactHodgeCertificate.RatGroupRing G}
    {q : K → I → ExactHodgeCertificate.RatGroupRing G}
    {R : I → I → ExactHodgeCertificate.RatGroupRing G} {c r : ℚ}
    (C : ExactHodgeCertificate.Certificate
      (ExactHodgeCertificate.generatorCoboundary s) B q R c r) :
    SharpExistence :=
  sharpExistence_of_hodgeCertificate hcheap.1 hcheap.2 hI s hgen C

end Hyperbolic
end GroupApproximation
