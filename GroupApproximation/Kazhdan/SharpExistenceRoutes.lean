import GroupApproximation.Kazhdan.TorsionFreeHyperbolicKazhdan
import GroupApproximation.Algebra.HyperbolicQuasiIsometry
import Mathlib.GroupTheory.Index

/-!
# The two routes to `SharpExistence`, as typed inputs

This module proves no new mathematics: what it does is turn "an infinite
torsion-free hyperbolic Kazhdan group exists, by the literature" into a statement
about named inputs, so that the distance between this repository and that theorem
is measured rather than asserted.

`Kazhdan/TorsionFreeHyperbolicKazhdan.lean` states `SharpExistence`.  The
literature reaches it two ways, and the two behave very differently as
formalization targets.

## The random-group route adds nothing

`RandomGroupInput` records the conclusion of the random-group theorems (Gromov;
Ollivier; Zuk, as used by Ollivier--Wise): at density `1/3 < d < 1/2` a random
group is infinite, finitely presented, torsion-free, hyperbolic and Kazhdan.
Its field list *is* the clause list of `SharpExistence`, so
`sharpExistence_of_randomGroupInput` is bookkeeping --- and
`randomGroupInput_of_sharpExistence` proves the converse, which is the honest
measurement: this route is not a reduction of `SharpExistence` to anything, it
is a citation for it.  Formalizing it means formalizing the density model and
Zuk's spectral criterion outright.

## The lattice route reduces to permanence properties

`LatticeRouteInput` records the other route: a cocompact lattice `Γ` in
`Sp(n,1)` --- infinite, finitely presented, hyperbolic because the symmetric
space is negatively curved, Kazhdan by Kostant --- together with a torsion-free
finite-index subgroup, which is Selberg's lemma.  Passing to that subgroup is
what buys torsion-freeness, and `sharpExistence_of_latticeRoute` shows what the
passage costs: three permanence statements, that hyperbolicity, property `(T)`
and finite presentation survive passage to a finite-index subgroup.

That is a real measurement, and its content is a warning.
`HyperbolicFiniteIndexPermanence` is an instance of
`Hyperbolic.QuasiIsometryInvariant` --- a finite-index subgroup is
quasi-isometric to the ambient group --- so the lattice route to `SharpExistence`
passes through exactly the Morse lemma that
`Algebra/HyperbolicQuasiIsometry.lean` records as missing.  The two open problems
in this development are not independent.

None of the three permanence statements is proved *in this module*, none is
assumed anywhere, and no theorem below is unconditional: each takes its inputs
explicitly.  Two of the three have since moved:
`Kazhdan/KazhdanFiniteIndex.lean` **proves** the property `(T)` one, and
`Kazhdan/LatticeRouteRemainder.lean` reduces the other two to the Morse lemma
and to Schreier's index formula respectively, and reassembles the route
(`FiniteIndex.sharpExistence_of_latticeRoute_of_inputs`).
-/

namespace GroupApproximation
namespace Hyperbolic

/-! ## The random-group route -/

/-- **The conclusion of the random-group theorems**, as an input.  Every field is
a clause of `SharpExistence`; see the module docstring for why that is the
point. -/
structure RandomGroupInput where
  /-- The random group. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  [fpCarrier : Group.IsFinitelyPresented Carrier]
  [infiniteCarrier : Infinite Carrier]
  /-- Torsion-free, as random groups at density below `1/2` are. -/
  torsionFree : IsPowerTorsionFree Carrier
  /-- Hyperbolic, by Gromov's density theorem. -/
  hyperbolic : IsHyperbolicGroup Carrier
  /-- Kazhdan, by Zuk's criterion at density above `1/3`. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Carrier

instance randomGroupInputGroup (R : RandomGroupInput) : Group R.Carrier :=
  R.groupCarrier

/-- The random-group route reaches the sharp statement --- by bookkeeping. -/
theorem sharpExistence_of_randomGroupInput (R : RandomGroupInput) : SharpExistence :=
  ⟨R.Carrier, R.groupCarrier, R.infiniteCarrier, R.fpCarrier, R.torsionFree,
    R.hyperbolic, R.kazhdan⟩

/-- ... and the sharp statement reaches the input, so the route is a citation
rather than a reduction. -/
theorem randomGroupInput_of_sharpExistence (h : SharpExistence) :
    Nonempty RandomGroupInput := by
  obtain ⟨G, inst, hinf, hfp, htf, hhyp, hT⟩ := h
  exact ⟨{ Carrier := G
           groupCarrier := inst
           fpCarrier := hfp
           infiniteCarrier := hinf
           torsionFree := htf
           hyperbolic := hhyp
           kazhdan := hT }⟩

/-! ## The lattice route -/

/-- **Hyperbolicity survives passage to a finite-index subgroup.**  An instance
of `QuasiIsometryInvariant`, since a finite-index subgroup is quasi-isometric to
the ambient group --- and that last clause is no longer a remark:
`Algebra/FiniteIndexQuasiIsometry.lean` proves the quasi-isometry, so
`FiniteIndex.hyperbolicFiniteIndexPermanence_of_quasiIsometryInvariant` derives
this statement from `QuasiIsometryInvariant` alone.  Not proved here. -/
def HyperbolicFiniteIndexPermanence : Prop :=
  ∀ (Γ : Type) (_ : Group Γ) (Λ : Subgroup Γ), Λ.FiniteIndex →
    IsHyperbolicGroup Γ → IsHyperbolicGroup ↥Λ

/-- **Property `(T)` survives passage to a finite-index subgroup.**
Bekka--de la Harpe--Valette, Theorem 1.7.1 --- and **a theorem of this
repository**: `Kazhdan/KazhdanFiniteIndex.lean` proves it, by induction of
representations, as `FiniteIndex.kazhdanFiniteIndexPermanence`.  It is kept as a
named `Prop` so that `sharpExistence_of_latticeRoute` below can be read as a
reduction, with its inputs visible. -/
def KazhdanFiniteIndexPermanence : Prop :=
  ∀ (Γ : Type) (_ : Group Γ) (Λ : Subgroup Γ), Λ.FiniteIndex →
    HasKazhdanPropertyT.{0, 0} Γ → HasKazhdanPropertyT.{0, 0} ↥Λ

/-- **Finite presentation survives passage to a finite-index subgroup.**
Reidemeister--Schreier.  `Algebra/ReidemeisterSchreier.lean` proves the
rewriting theorem and reduces this statement to one input --- that a
finite-index subgroup of a finitely generated free group is finitely presented
--- and `FiniteIndex.finitePresentationFiniteIndexPermanence_of_freeInput`
is that reduction. -/
def FinitePresentationFiniteIndexPermanence : Prop :=
  ∀ (Γ : Type) (_ : Group Γ) (Λ : Subgroup Γ), Λ.FiniteIndex →
    Group.IsFinitelyPresented Γ → Group.IsFinitelyPresented ↥Λ

/-- **The lattice route's inputs.**  A cocompact lattice in `Sp(n,1)` and the
torsion-free finite-index subgroup Selberg's lemma supplies.  Torsion-freeness
is asked of the subgroup, not of the lattice, which is exactly the shape of the
argument. -/
structure LatticeRouteInput where
  /-- The lattice `Γ`, which may well have torsion. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  [fpCarrier : Group.IsFinitelyPresented Carrier]
  [infiniteCarrier : Infinite Carrier]
  /-- Hyperbolic: the lattice is cocompact in a negatively curved symmetric
  space. -/
  hyperbolic : IsHyperbolicGroup Carrier
  /-- Kazhdan, by Kostant's theorem for `Sp(n,1)`. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Carrier
  /-- Selberg's finite-index subgroup. -/
  Sub : Subgroup Carrier
  /-- It has finite index. -/
  subFiniteIndex : Sub.FiniteIndex
  /-- It is torsion-free --- this is what the passage buys. -/
  subTorsionFree : IsPowerTorsionFree ↥Sub
  /-- It is infinite, being of finite index in an infinite group. -/
  subInfinite : Infinite ↥Sub

instance latticeRouteInputGroup (L : LatticeRouteInput) : Group L.Carrier :=
  L.groupCarrier

/-- **The lattice route reaches the sharp statement, at the price of three
permanence properties.**  Torsion-freeness comes from Selberg's subgroup; every
other clause has to be carried across the finite-index passage, and
`HyperbolicFiniteIndexPermanence` is the one that is an instance of the Morse
lemma. -/
theorem sharpExistence_of_latticeRoute
    (h₁ : HyperbolicFiniteIndexPermanence)
    (h₂ : KazhdanFiniteIndexPermanence)
    (h₃ : FinitePresentationFiniteIndexPermanence)
    (L : LatticeRouteInput) : SharpExistence :=
  ⟨↥L.Sub, inferInstance, L.subInfinite,
    h₃ L.Carrier L.groupCarrier L.Sub L.subFiniteIndex L.fpCarrier,
    L.subTorsionFree,
    h₁ L.Carrier L.groupCarrier L.Sub L.subFiniteIndex L.hyperbolic,
    h₂ L.Carrier L.groupCarrier L.Sub L.subFiniteIndex L.kazhdan⟩

end Hyperbolic
end GroupApproximation
