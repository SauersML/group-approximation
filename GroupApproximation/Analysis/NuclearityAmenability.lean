import GroupApproximation.Analysis.PropertyTNonamenable
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Sofic.LiteralBaseTranslationLattice

/-!
# Nonamenability of the literal base, and the Lance debt

The paragraph immediately after the proof of Theorem D in
`non_mf_groups_exist.tex` (lines 1097--1102 of the working copy at the time of
writing; **navigate by the anchor string "The algebra is not nuclear"**, since
concurrent sessions are renumbering the file continuously) reads

> The algebra is not nuclear: the canonical map `\mathcal B → E` is injective
> (Section `sec:proofA`), so `E` contains an infinite Kazhdan group and is
> nonamenable, whence `\Cred(E)` is not nuclear [Lance].  The nuclear form of
> the Blackadar--Kirchberg problem --- whether every stably finite separable
> nuclear `C^*`-algebra is quasidiagonal --- therefore remains open.

Two classical inputs are used there.  This module records the state of both.

## Input 1: nonamenability of infinite Kazhdan groups --- PROVED

`GroupApproximation.Analysis.PropertyTNonamenable` proves, with no hypothesis
standing in for mathematics, that an infinite group with property `(T)` admits
no left-invariant mean on its bounded functions.  Here that general theorem is
instantiated at the manuscript's own object: `infinite_base` shows that the
literal twenty-relator affine base `Base` is infinite (its translation lattice
`ℤ³` embeds), and `base_not_hasInvariantMean` combines this with the
premise-free property-`(T)` certificate
`LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT`.  So the sub-clause
"`\mathcal B` is an infinite Kazhdan group, and is therefore nonamenable" is
machine-checked at the literal group.  Passing from there to "`E` ... is
nonamenable" is `not_isAmenable_of_base_embeds`, which still consumes the
injectivity of `\mathcal B → E` as an explicit hypothesis (see the last part
of this docstring).

Both of the repository's amenability predicates are covered, so there is no
choice-of-definition gap.  `base_not_isAmenable` refutes
`Amenability.IsAmenable` --- the primary predicate, a left-invariant finitely
additive probability measure on all subsets --- through the Følner route,
which consumes `AmenableActionSofic.exists_folner` and therefore the
repository's own Tarski--Hall theorem.  `base_not_hasInvariantMean` refutes
`Amenability.HasInvariantMean` --- the textbook invariant mean on bounded
functions, and the notion Lance's theorem consumes.  The second follows from
the first through `Amenability.isAmenable_of_hasInvariantMean`, and is in
addition proved independently by the Reiter/Day route of
`PropertyTNonamenable`.

## Input 2: Lance's theorem --- UNSTATABLE, a foundations gap

Lance's theorem (E. C. Lance, *On nuclear `C^*`-algebras*, J. Funct. Anal. 12
(1973) 157--176) says that for a discrete group `G` the reduced group
`C^*`-algebra `C^*_λ(G)` is nuclear if and only if `G` is amenable.  The
manuscript uses one direction once: `C^*_λ(G)` nuclear implies `G` amenable,
contrapositively `G` nonamenable implies `C^*_λ(G)` not nuclear, applied to
`G = E`.  It is the harder of the two directions; the easy one is not used, so
there is no cheap half to harvest.

This is **not a proof gap but a foundations gap: the statement cannot be
written down in Lean at all** at the pinned Mathlib revision
(`905b95818eb32af7874a58b427f50c1711a5e96c`).  Nuclearity of a `C^*`-algebra
`A` is the assertion that the identity of `A ⊗_min B` and of `A ⊗_max B` agree
for all `B`, or equivalently that `A` has the completely positive
approximation property.  Neither notion exists:

* A case-insensitive search for "nuclear" over Mathlib returns **nothing**,
  and over `GroupApproximation/` also nothing.
* There is no `C^*`-tensor product in Mathlib, minimal or maximal.  (A
  concurrent lane of this repository is building the minimal tensor product
  from the ground up --- `Analysis/CStarTensorProduct*.lean` at the time of
  writing.  Nuclearity sits above that layer and stays out of scope here.)
  The whole of `Mathlib/Analysis/CStarAlgebra/` is ApproximateUnit, Basic,
  CStarMatrix,
  Classes, CompletelyPositiveMap, ContinuousFunctionalCalculus/,
  ContinuousLinearMap, ContinuousMap, Exponential, Extreme, Fuglede,
  GelfandDuality, GelfandNaimarkSegal, Hom, Matrix, Module/, Multiplier,
  PositiveLinearMap, Projection, SpecialFunctions/, Spectrum, Unitary/,
  Unitization, lpSpace.
* What *does* exist is the bare definition of a completely positive map
  (`CompletelyPositiveMap`, notation `A₁ →CP A₂`, in
  `Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap`) plus the single fact
  that star algebra homomorphisms are completely positive.  That partially
  seeds the CPAP side of a future nuclearity definition, and nothing more:
  there is no Stinespring dilation, no approximation property, and no
  injectivity or hyperfiniteness of von Neumann algebras.

Even granting a definition, every published proof of the needed direction
factors through the missing machinery.  The standard route (Brown--Ozawa,
Theorem 2.6.8) runs `C^*_λ(G)` nuclear ⟹ the completely positive
approximation property ⟹ (Stinespring, plus the canonical trace) a net of
finitely supported positive-definite functions on `G` tending to `1`
pointwise ⟹ Reiter's condition ⟹ an invariant mean.  The alternative route
runs through Connes' theorem that injective von Neumann algebras are
hyperfinite, which is heavier still.  Only the *last* leg exists here, and in
the opposite direction: `PropertyTNonamenable.exists_reiter_of_functionMean`
is the implication invariant mean ⟹ Reiter.

There is no cheaper route for this particular `E`.  The obvious shortcut ---
find a free subgroup of `E` and quote nonnuclearity of `C^*_λ(F_2)` --- buys
nothing even if the free subgroup is produced: nonnuclearity of `C^*_λ(F_2)`
is itself normally deduced from Lance, and transferring it from
`C^*_λ(F_2)` up to `C^*_λ(E)` needs permanence of nuclearity under the
canonical conditional expectation onto a subgroup algebra, which is just as
unformalized.  The structural features of `E` that the manuscript does
formalize (the Clifford sign, the lamp kernel, the compression defect) bear on
MF-ness, not on nuclearity.

**Scope note for the reader of the manuscript.**  The nonnuclearity paragraph
is not load-bearing.  Theorem D asserts that `\Cred(E)` is unital, separable,
carries a faithful tracial state, is therefore stably finite, and is not an MF
algebra, and its printed proof (the `proof` environment directly above the
paragraph) invokes only countability of `E`, the faithful-trace lemma, and
Theorem A.  Nonnuclearity is raised only afterwards, to observe that the
example does not settle the *nuclear* form of the Blackadar--Kirchberg
problem.  No theorem of the manuscript depends on it.

## What is still needed to reach "`E` ... is nonamenable"

`PropertyTNonamenable.not_isAmenable_of_infinite_kazhdan_subgroup` transports
nonamenability along an injective homomorphism (and
`not_hasInvariantMean_of_surjective` below transports it along a quotient
map).  Applying it to `LiteralNonMFPresentation.baseMap : Base →* MarkedGroup`
needs `Function.Injective baseMap`, the manuscript's "the canonical map
`\mathcal B → E` is injective" (proved there by composing with `E → W`, using
that `\mathcal B → \bar\Gamma` is an isomorphism and that the level-zero map
`j` is injective).  That injectivity statement does not exist in the
repository at the time of writing; it is a separate formalization target, not
a literature input, so it is left as an explicit hypothesis of
`not_isAmenable_of_base_embeds` rather than assumed anywhere.  Supplying it
turns that declaration into the manuscript's sentence verbatim.
-/

namespace GroupApproximation
namespace NuclearityAmenability

open Amenability

/-! ## Amenability passes to quotients -/

section Quotient

variable {G H : Type*} [Group G] [Group H]

/-- Pushing an invariant mean forward along a surjection. -/
noncomputable def quotientFunctionMean (f : G →* H) (hf : Function.Surjective f)
    (m : FunctionMean G) : FunctionMean H where
  eval k := m.eval (fun x : G ↦ k (f x))
  eval_add k l hk hl := by
    have hbk : IsBddFun (fun x : G ↦ k (f x)) := by
      obtain ⟨C, hC⟩ := hk; exact ⟨C, fun x ↦ hC _⟩
    have hbl : IsBddFun (fun x : G ↦ l (f x)) := by
      obtain ⟨C, hC⟩ := hl; exact ⟨C, fun x ↦ hC _⟩
    exact m.eval_add (fun x : G ↦ k (f x)) (fun x : G ↦ l (f x)) hbk hbl
  eval_nonneg k hk hpos := by
    refine m.eval_nonneg _ ?_ fun x ↦ hpos _
    obtain ⟨C, hC⟩ := hk
    exact ⟨C, fun x ↦ hC _⟩
  eval_const c := m.eval_const c
  eval_invariant h k hk := by
    obtain ⟨g, rfl⟩ := hf h
    have hb : IsBddFun (fun x : G ↦ k (f x)) := by
      obtain ⟨C, hC⟩ := hk
      exact ⟨C, fun x ↦ hC _⟩
    calc m.eval (fun x : G ↦ k (f g * f x))
        = m.eval (fun x : G ↦ k (f (g * x))) := by
          congr 1
          funext x
          rw [map_mul]
      _ = m.eval (fun x : G ↦ k (f x)) := m.eval_invariant g _ hb

/-- Amenability in the invariant-mean sense passes to quotients. -/
theorem hasInvariantMean_of_surjective (f : G →* H) (hf : Function.Surjective f)
    (h : HasInvariantMean G) : HasInvariantMean H := by
  obtain ⟨m⟩ := h
  exact ⟨quotientFunctionMean f hf m⟩

/-- Nonamenability of a quotient forces nonamenability of the group. -/
theorem not_hasInvariantMean_of_surjective (f : G →* H)
    (hf : Function.Surjective f) (hH : ¬ HasInvariantMean H) :
    ¬ HasInvariantMean G := fun hG ↦ hH (hasInvariantMean_of_surjective f hf hG)

end Quotient

/-! ## The literal base is infinite -/

/-- **The literal twenty-relator affine base is infinite.**  Its translation
subgroup is a copy of `ℤ³`: the lattice homomorphism
`LiteralBaseTranslationLattice.latticeToBase` is injective, so already the
first coordinate axis embeds `ℤ` into the base. -/
theorem infinite_base : Infinite LiteralNonMFPresentation.Base := by
  refine Infinite.of_injective
    (fun n : ℤ ↦ LiteralBaseTranslationLattice.latticeToBase
      (Multiplicative.ofAdd (Pi.single (0 : Fin 3) n))) ?_
  intro a b hab
  have h1 : (Multiplicative.ofAdd (Pi.single (0 : Fin 3) a) :
        Multiplicative (Fin 3 → ℤ))
      = Multiplicative.ofAdd (Pi.single (0 : Fin 3) b) :=
    LiteralBaseTranslationLattice.latticeToBase_injective hab
  have h2 : (Pi.single (0 : Fin 3) a : Fin 3 → ℤ) = Pi.single (0 : Fin 3) b :=
    Multiplicative.ofAdd.injective h1
  have h3 := congrFun h2 (0 : Fin 3)
  simpa using h3

/-! ## The manuscript clause, at the literal group -/

/-- **"`\mathcal B` is an infinite Kazhdan group, hence nonamenable", at the
literal base.**  Unconditional, in the repository's primary amenability
predicate: the property-`(T)` certificate for the base is premise-free,
infiniteness is `infinite_base`, and nonamenability is
`PropertyTNonamenable.infinite_kazhdan_not_isAmenable`. -/
theorem base_not_isAmenable : ¬ IsAmenable LiteralNonMFPresentation.Base := by
  haveI := infinite_base
  exact PropertyTNonamenable.infinite_kazhdan_not_isAmenable
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT

/-- The same in the invariant-mean form, which is the notion Lance's theorem
consumes.  It also follows from `base_not_isAmenable` through
`Amenability.isAmenable_of_hasInvariantMean`; the proof recorded here is the
independent Reiter/Day route. -/
theorem base_not_hasInvariantMean :
    ¬ HasInvariantMean LiteralNonMFPresentation.Base := by
  haveI := infinite_base
  exact PropertyTNonamenable.infinite_kazhdan_not_hasInvariantMean
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT

/-- **Every group containing an isomorphic copy of the literal base is
nonamenable.**  This is the shape in which the manuscript uses the clause:
with `f = LiteralNonMFPresentation.baseMap` and its (not yet formalized)
injectivity, it reads "`E` contains an infinite Kazhdan group and is
nonamenable". -/
theorem not_isAmenable_of_base_embeds {G : Type} [Group G]
    (f : LiteralNonMFPresentation.Base →* G) (hf : Function.Injective f) :
    ¬ IsAmenable G := by
  haveI := infinite_base
  exact PropertyTNonamenable.not_isAmenable_of_infinite_kazhdan_subgroup
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT f hf

/-- The invariant-mean form of the same transport. -/
theorem not_hasInvariantMean_of_base_embeds {G : Type*} [Group G]
    (f : LiteralNonMFPresentation.Base →* G) (hf : Function.Injective f) :
    ¬ HasInvariantMean G :=
  PropertyTNonamenable.not_hasInvariantMean_of_injective f hf
    base_not_hasInvariantMean

end NuclearityAmenability
end GroupApproximation
