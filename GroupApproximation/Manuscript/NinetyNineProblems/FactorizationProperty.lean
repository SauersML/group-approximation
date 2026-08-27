import GroupApproximation.Manuscript.NinetyNineProblems.ProblemX
import GroupApproximation.Kazhdan.Kazhdan
import GroupApproximation.Algebra.FiniteResidual
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarNotNuclear
import GroupApproximation.Meta.AxiomGuard

/-!
# Kirchberg's factorization property, and which groups are known to fail it

`Manuscript/NinetyNineProblems/ProblemX.lean` leaves one clause open: whether
the canonical trace of `C⋆(E)` is an **amenable** trace.  That clause has a
group-theoretic name, and this file gives it one, states the theorem of
Kirchberg's that constrains it, and proves the constraint bites on the
manuscript's *other* headline group.

## The property, and which side of the equivalence is the definition

A discrete group `G` has **Kirchberg's factorization property** when the map
`λ ⊙ ρ` sending `a ⊗ b` to `λ(a) ρ(b)` --- left and right regular
representations on `ℓ²(G)` --- is continuous for the **minimal** tensor norm on
`C⋆(G) ⊙ C⋆(G)`, so that it extends to `C⋆(G) ⊗_min C⋆(G)`.  That is
Kirchberg's own formulation.

Brown, *Invariant means and finite representation theory of C⋆-algebras*,
Mem. Amer. Math. Soc. **184** (2006), no. 865, Theorem 4.1.9, proves that for a
discrete group this is **equivalent** to amenability of the canonical trace on
`C⋆(G)`.  `HasFactorizationProperty` below takes the *trace* side as the
definition, because that is the side this development can consume:
`Quasidiagonal.IsAmenableTrace` is already the transcription of Brown's
amenable traces, and the tensor-norm formulation has no definition here.

**So the equivalence is a citation and not a theorem below.**  Nothing in this
file proves that the trace condition implies the tensor-norm condition or
conversely; every statement here is about the trace condition, and the name
`HasFactorizationProperty` is justified by Brown's theorem rather than by
anything machine-checked.

## Kirchberg's constraint, and the elementary half proved here

Kirchberg, *Discrete groups with Kazhdan's property T and factorization
property are residually finite*, Math. Ann. **299** (1994), 551--563, proves
that a Kazhdan group with the factorization property is residually finite.
That is `KirchbergKazhdanFactorizationInput`, an assumed input; no inhabitant
is constructed.

What *is* proved here is the elementary complement:
`not_isResiduallyFinite_of_isSimpleGroup_of_infinite`, that an infinite simple
group is not residually finite.  The argument is the normal-core one: a
finite-index subgroup `L` contains the finite-index normal subgroup
`L.normalCore`, simplicity forces that core to be `⊥` or `⊤`, `⊥` would make
the quotient map injective into a finite group and so make `G` finite, and `⊤`
forces `L = ⊤`.  So every finite-index subgroup is everything, and the finite
residual is not trivial.

Put together: **an infinite simple Kazhdan group fails the factorization
property**, so its canonical trace on the full group C⋆-algebra is not an
amenable trace.

## The manuscript's headline group is on the wrong side of this

`Manuscript/OneSidedMFRadical` proves, unconditionally, that the rank-twelve
binary Leavitt elementary group `H = EL₁₂(L_{F₂}(1,2))` is simple
(`RankTwelveEndpoint.manuscriptPropositionSimple`), infinite
(`rankTwelveEndpoint_infinite`), countable and Kazhdan
(`RankTwelveEndpoint.hasKazhdanPropertyT`).  So `H` is not residually finite
--- proved outright below, with no input --- and, granted Kirchberg's theorem,
`H` does not have the factorization property.

**That is why `H` says nothing about STW Problem X(1).**  Problem X(1) asks
whether every *amenable* trace is quasidiagonal; the canonical trace of
`C⋆(H)` is not amenable, so `H` cannot be a counterexample to it however badly
`H` fails to be MF.  The literal group `E` of `ProblemX.lean` is the open leaf
precisely because nothing forces its trace off the amenable side: `E` is not
known to be simple, and `LiteralFactorizationProperty` is not known either
way.

## Thom's refutation, in the same vocabulary

The same input refutes the general implication *sofic ⟹ factorization
property*.  Thom, *Examples of hyperlinear groups without factorization
property*, Groups Geom. Dyn. **4** (2010), 195--208 (arXiv:0810.2180),
constructs LEF --- so sofic --- Kazhdan groups that are not residually finite;
that is `ThomSoficKazhdanNonResiduallyFiniteInput`, also an assumed input.
Against Kirchberg's theorem it gives
`not_forall_sofic_hasFactorizationProperty`, and through
`isHyperlinear_of_isSofic` the hyperlinear form.  Those two are the precise
statement of the warning printed in `ProblemX.lean`: soficity of `E` cannot
supply `LiteralFactorizationProperty`, because soficity does not supply the
factorization property for anyone.
-/

namespace GroupApproximation
namespace NinetyNineProblems

open LiteralNonMFPresentation
open Manuscript.OneSidedMFRadical

universe u

/-! ## The factorization property, at the trace side of Brown's equivalence -/

/-- **Kirchberg's factorization property** for a discrete group `G`, stated at
the trace side of Brown's equivalence: the canonical trace of the full group
C⋆-algebra `C⋆(G)` is an amenable trace.

Kirchberg's own definition asks that `a ⊗ b ↦ λ(a) ρ(b)` be continuous for the
minimal tensor norm on `C⋆(G) ⊙ C⋆(G)`; Brown, Mem. AMS **184** (2006),
Theorem 4.1.9, proves the two conditions equivalent for discrete groups.  The
equivalence is **cited, not proved here** --- the tensor-norm side has no
definition in this development --- so every theorem below is literally about
the trace.

Only `[Group G]` is required, which is exactly what `MaximalGroupCStar` and
`canonicalMaximalTrace` need.  Countability is not part of the property and is
imposed only where a cited theorem imposes it. -/
def HasFactorizationProperty (G : Type u) [Group G] : Prop :=
  Quasidiagonal.IsAmenableTrace
    (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)

/-- The open clause of `Manuscript/NinetyNineProblems/ProblemX.lean` is the
factorization property for `E`, on the nose: `LiteralFactorizationProperty`
and `HasFactorizationProperty MarkedGroup` are the same proposition, not
merely equivalent ones. -/
theorem literalFactorizationProperty_iff :
    LiteralFactorizationProperty ↔ HasFactorizationProperty MarkedGroup :=
  Iff.rfl

/-! ## Kirchberg's theorem, as a typed input -/

/-- **Kirchberg's theorem, as a typed input.**

> Kirchberg, *Discrete groups with Kazhdan's property T and factorization
> property are residually finite*, Math. Ann. **299** (1994), 551--563: a
> countable group with property `(T)` and the factorization property is
> residually finite.

No inhabitant is constructed here and none should be: the proof runs through
the tensor-norm formulation of the factorization property, which this
development does not define, and through the Kazhdan projection in
`C⋆(G) ⊗_min C⋆(G)`.  It is a structure rather than a bare implication so
that consuming it leaves a visible binder in the type of every theorem that
does.

The Kazhdan hypothesis is read at representation-space universe `u`, matching
`HasKazhdanPropertyT.{0, 0}` as the repository states it for concrete groups;
for a countable group property `(T)` does not depend on that choice, and
nothing below needs it to. -/
structure KirchbergKazhdanFactorizationInput : Prop where
  /-- A countable Kazhdan group with the factorization property is residually
  finite. -/
  residuallyFinite : ∀ (G : Type u) [Group G] [Countable G],
    HasKazhdanPropertyT.{u, u} G → HasFactorizationProperty G →
      IsResiduallyFinite G

/-! ## Infinite simple groups are not residually finite -/

/-- **An infinite simple group is not residually finite.**

Proved outright.  Let `L` be a finite-index subgroup.  Its normal core
`L.normalCore` is normal and still of finite index, so simplicity leaves two
cases.  If the core is `⊥` then the quotient map `G → G ⧸ L.normalCore` has
trivial kernel, hence is injective into a finite group, making `G` finite and
contradicting `Infinite G`.  So the core is `⊤`, and since it sits inside `L`
we get `L = ⊤`.  Every finite-index subgroup is therefore the whole group, and
`isResiduallyFinite_iff` --- which asks for a finite-index subgroup *missing* a
given nontrivial element --- fails at every such element.

Note what this does *not* need: no hypothesis on generation, no property `(T)`,
and no analysis.  It is the reason the manuscript's headline group can be
placed on the non-factorization side by a citation alone. -/
theorem not_isResiduallyFinite_of_isSimpleGroup_of_infinite
    (G : Type u) [Group G] [IsSimpleGroup G] [Infinite G] :
    ¬ IsResiduallyFinite G := by
  intro hrf
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  obtain ⟨L, hL, hxL⟩ := isResiduallyFinite_iff.mp hrf x hx
  haveI := hL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L.normalCore inferInstance with
    hbot | htop
  · haveI : (L.normalCore).FiniteIndex := inferInstance
    haveI : Finite (G ⧸ L.normalCore) :=
      L.normalCore.finite_quotient_of_finiteIndex
    have hinj : Function.Injective (QuotientGroup.mk' L.normalCore) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hbot
    haveI : Finite G := Finite.of_injective _ hinj
    exact not_finite G
  · refine hxL ?_
    have hmem : x ∈ L.normalCore := by
      rw [htop]
      exact Subgroup.mem_top x
    exact L.normalCore_le hmem

/-- **An infinite simple Kazhdan group fails the factorization property.**

Kirchberg's theorem contrapositive, with the elementary half supplied by
`not_isResiduallyFinite_of_isSimpleGroup_of_infinite`.  The whole cost is the
leading binder `k`. -/
theorem not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan
    (k : KirchbergKazhdanFactorizationInput.{u}) (G : Type u) [Group G]
    [Countable G] [IsSimpleGroup G] [Infinite G]
    (hT : HasKazhdanPropertyT.{u, u} G) :
    ¬ HasFactorizationProperty G := fun hfp ↦
  not_isResiduallyFinite_of_isSimpleGroup_of_infinite G
    (k.residuallyFinite G hT hfp)

/-! ## The manuscript's headline group -/

/-- **The rank-twelve binary Leavitt elementary group is not residually
finite.**  Unconditional: `H` is simple
(`RankTwelveEndpoint.manuscriptPropositionSimple`, the manuscript's
`prop:simple`) and infinite (`rankTwelveEndpoint_infinite`, which transports
infiniteness of the coefficient ring through the elementary root `e₀₁`), and
an infinite simple group is not residually finite.

This is a fact about `H` that the manuscript never needed and never states.
It is recorded here because it is the step that puts `H` outside the reach of
Problem X(1). -/
theorem rankTwelveLeavitt_not_isResiduallyFinite :
    ¬ IsResiduallyFinite RankTwelveEndpoint.H := by
  haveI : IsSimpleGroup RankTwelveEndpoint.H :=
    RankTwelveEndpoint.manuscriptPropositionSimple
  haveI : Infinite RankTwelveEndpoint.H := rankTwelveEndpoint_infinite
  exact not_isResiduallyFinite_of_isSimpleGroup_of_infinite RankTwelveEndpoint.H

/-- **The manuscript's headline group does not have the factorization
property**, so the canonical trace of `C⋆(H)` is not an amenable trace.

`H` is countable, simple, infinite and Kazhdan --- all four unconditionally,
in `Manuscript/OneSidedMFRadical` --- so Kirchberg's theorem applies to the
contrapositive.

**This is why `H` is silent about STW Problem X(1).**  X(1) asks whether every
amenable trace is quasidiagonal.  `H` fails to be MF as loudly as the
manuscript's headline says, and none of that is a counterexample to X(1),
because the hypothesis of X(1) is not met at `H`'s canonical trace.  The
literal group `E` of `Manuscript/NinetyNineProblems/ProblemX.lean` is the open
leaf for the opposite reason: `E` is not known to be simple, so nothing here
pushes `LiteralFactorizationProperty` either way. -/
theorem rankTwelveLeavitt_not_hasFactorizationProperty
    (k : KirchbergKazhdanFactorizationInput.{0}) :
    ¬ HasFactorizationProperty RankTwelveEndpoint.H := by
  haveI : Countable RankTwelveEndpoint.H := RankTwelveEndpoint.countable
  haveI : IsSimpleGroup RankTwelveEndpoint.H :=
    RankTwelveEndpoint.manuscriptPropositionSimple
  haveI : Infinite RankTwelveEndpoint.H := rankTwelveEndpoint_infinite
  exact not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan k
    RankTwelveEndpoint.H RankTwelveEndpoint.hasKazhdanPropertyT

/-! ## Thom: soficity does not give the factorization property -/

/-- **Thom's examples, as a typed input.**

> Thom, *Examples of hyperlinear groups without factorization property*,
> Groups Geom. Dyn. **4** (2010), 195--208 (arXiv:0810.2180): there are
> countable LEF groups --- so sofic, so hyperlinear --- with property `(T)`
> that are not residually finite.

The existential is stated over the group together with its group and
countability structure, since a `Type u` alone carries neither.  No inhabitant
is constructed: the construction is a limit of finite quotients of Kazhdan
lattices and is not formalized here. -/
structure ThomSoficKazhdanNonResiduallyFiniteInput : Prop where
  /-- A countable sofic Kazhdan group that is not residually finite. -/
  exists_group : ∃ (G : Type u) (_ : Group G) (_ : Countable G),
    IsSofic G ∧ HasKazhdanPropertyT.{u, u} G ∧ ¬ IsResiduallyFinite G

/-- **Soficity does not imply the factorization property.**

Thom's group is sofic, so an implication *sofic ⟹ factorization property*
would give it the factorization property; with property `(T)` Kirchberg's
theorem would then make it residually finite, which it is not.

Both inputs are leading binders, and neither is inhabited here.  This is the
exact statement behind the warning in
`Manuscript/NinetyNineProblems/ProblemX.lean`: no argument that uses only
soficity of `E` can produce `LiteralFactorizationProperty`. -/
theorem not_forall_sofic_hasFactorizationProperty
    (k : KirchbergKazhdanFactorizationInput.{u})
    (t : ThomSoficKazhdanNonResiduallyFiniteInput.{u}) :
    ¬ ∀ (G : Type u) [Group G] [Countable G],
        IsSofic G → HasFactorizationProperty G := by
  intro hall
  obtain ⟨G, hgroup, hcount, hsofic, hT, hnrf⟩ := t.exists_group
  letI := hgroup
  letI := hcount
  exact hnrf (k.residuallyFinite G hT (hall G hsofic))

/-- **Hyperlinearity does not imply the factorization property.**  The same
witness, pushed through `isHyperlinear_of_isSofic`: a sofic model of accuracy
`ε/2` becomes a hyperlinear model of accuracy `ε` under
`σ ↦ σ⁻¹.permMatrix`.

Stated separately because the hyperlinear form is the one the trace-class
statements of `ProblemX.lean` are phrased against: what soficity of `E`
delivers there is a hyperlinear trace, and this says that the delivery cannot
be upgraded by a general theorem. -/
theorem not_forall_hyperlinear_hasFactorizationProperty
    (k : KirchbergKazhdanFactorizationInput.{u})
    (t : ThomSoficKazhdanNonResiduallyFiniteInput.{u}) :
    ¬ ∀ (G : Type u) [Group G] [Countable G],
        IsHyperlinear G → HasFactorizationProperty G := by
  intro hall
  obtain ⟨G, hgroup, hcount, hsofic, hT, hnrf⟩ := t.exists_group
  letI := hgroup
  letI := hcount
  exact hnrf (k.residuallyFinite G hT (hall G (isHyperlinear_of_isSofic hsofic)))

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms HasFactorizationProperty
#audit_closed_axioms literalFactorizationProperty_iff
#audit_axioms KirchbergKazhdanFactorizationInput
#audit_axioms not_isResiduallyFinite_of_isSimpleGroup_of_infinite
#audit_axioms not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan
#audit_closed_axioms rankTwelveLeavitt_not_isResiduallyFinite
#audit_axioms rankTwelveLeavitt_not_hasFactorizationProperty
#audit_axioms ThomSoficKazhdanNonResiduallyFiniteInput
#audit_axioms not_forall_sofic_hasFactorizationProperty
#audit_axioms not_forall_hyperlinear_hasFactorizationProperty
