import GroupApproximation.Analysis.NuclearityBaseEmbedding
import GroupApproximation.Analysis.PropertyTNonamenable
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Sofic.LiteralBaseTranslationLattice

/-!
# Nonamenability of `E`, and the Lance debt

The paragraph immediately after the proof of Theorem D in
`non_mf_groups_exist.tex` (**navigate by the anchor string "The algebra is not
nuclear"**, since concurrent sessions renumber the file continuously) reads

> The algebra is not nuclear: the canonical map `\mathcal B → E` is injective
> (Section `sec:witness`), so `E` contains an infinite Kazhdan group and is
> nonamenable, whence `\Cred(E)` is not nuclear [Lance].  The nuclear form of
> the Blackadar--Kirchberg problem --- whether every stably finite separable
> nuclear `C^*`-algebra is quasidiagonal --- therefore remains open.

Three inputs are used there.  Two are proved in this repository and are
assembled here; the third is Lance's theorem, and this module records exactly
why it is out of reach and exactly how little of the paragraph depends on it.

## Input 1: injectivity of `\mathcal B → E` --- PROVED

`GroupApproximation.NuclearityBaseEmbedding.baseMap_injective` proves
the manuscript's opening clause at the literal group, by the manuscript's own
route: compose with the affine--Clifford witness `E → W` of Section
`sec:witness`, observe that the composite is the level-zero inclusion of the
exact affine matrix group, and use that the twenty relators present that group
(`LiteralBaseCompleteness.affineQuotient_injective`) and that the level-zero
map is injective (`MarkedCompression.iotaAmbient_injective`).

This clause is genuine content, not bookkeeping: Definition `def:E` introduces
`ι : \mathcal B → E` with the explicit warning that it "is not assumed to be
injective", and Theorems A--D are arranged never to need it.  Only this
paragraph does.

## Input 2: nonamenability of infinite Kazhdan groups --- PROVED

`GroupApproximation.Analysis.PropertyTNonamenable` proves, with no hypothesis
standing in for mathematics, that an infinite group with property `(T)` admits
no invariant mean.  Here that general theorem is instantiated at the
manuscript's own object: `infinite_base` shows that the literal twenty-relator
affine base is infinite (its translation lattice `ℤ³` embeds), and
`base_not_isAmenable` combines this with the premise-free property-`(T)`
certificate `LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT`.
Transporting along Input 1 gives `markedGroup_not_isAmenable`, which is the
paragraph's clause "`E` contains an infinite Kazhdan group and is
nonamenable" verbatim.

Both of the repository's amenability predicates are covered, so there is no
choice-of-definition gap.  `base_not_isAmenable` refutes
`Amenability.IsAmenable` --- the primary predicate, a left-invariant finitely
additive probability measure on all subsets --- through the Følner route,
which consumes `AmenableActionSofic.exists_folner` and therefore the
repository's own Tarski--Hall theorem.  `base_not_hasInvariantMean` refutes
`Amenability.HasInvariantMean` --- the textbook invariant mean on bounded
functions, and the notion Lance's theorem consumes --- and follows from the
first through `Amenability.isAmenable_of_hasInvariantMean`.

Mathlib supplies **nothing** on this side: it has no `IsAmenable`, no
`Amenable`, and no invariant mean (see item 8 of the inventory below).  Every
step therefore runs through this repository's own `Amenability` namespace, and
the chain is worth writing out once, since the ledger row for this sentence
has stood at MISSING on both statement and proof:

    LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT      (premise-free; on
                                                             the audit's
                                                             headline roster)
      ↓ LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT
    property (T) for the literal twenty-relator base
      ↓ with LiteralBaseTranslationLattice.latticeToBase_injective → infinite_base
      ↓ PropertyTNonamenable.infinite_kazhdan_not_isAmenable
        (Følner, via AmenableActionSofic.exists_folner = this repo's Tarski--Hall)
    base_not_isAmenable
      ↓ Amenability.IsAmenable.subgroup + HasKazhdanPropertyT.of_mulEquiv
      ↓ NuclearityBaseEmbedding.baseMap_injective            (Input 1)
    markedGroup_not_isAmenable
      ↓ Amenability.isAmenable_of_hasInvariantMean
    markedGroup_not_hasInvariantMean

No link carries a hypothesis standing in for mathematics, so the whole first
clause of the printed sentence --- "since the infinite Kazhdan group
`\mathcal B` is nonamenable, so is `E`" --- is unconditional.  Only the final
"hence `\Cred(E)` is not nuclear" remains, and it is Lance alone.

An earlier docstring here advertised a second, independent Reiter/Day route
through `PropertyTNonamenable.infinite_kazhdan_not_hasInvariantMean`, and a
transport through `PropertyTNonamenable.not_hasInvariantMean_of_injective`.
Neither declaration exists, in this revision or any earlier one, so neither
route was ever available and this module never built; being outside the root
import closure at the time, nothing in CI noticed.  The derivations from the
`IsAmenable` forms beside them are the proofs.

## Input 3: Lance's theorem --- a foundations gap, not a proof gap

Lance's theorem (E. C. Lance, *On nuclear `C^*`-algebras*, J. Funct. Anal. 12
(1973) 157--176) says that for a discrete group `G` the reduced group
`C^*`-algebra `C^*_λ(G)` is nuclear if and only if `G` is amenable.  The
manuscript uses one direction once: `C^*_λ(G)` nuclear implies `G` amenable,
contrapositively `G` nonamenable implies `C^*_λ(G)` not nuclear, applied to
`G = E`.  It is the harder of the two directions; the easy one is not used, so
there is no cheap half to harvest.

**How it is recorded here.**  Lance's theorem is *not* proved in this
repository and is *not* tagged, axiomatized, or hidden behind a Prop-valued
definition that nothing establishes.  It enters as an **explicit hypothesis**,
named `lance`, on exactly one declaration:
`reducedGroupCStar_not_nuclear_of_lance` at the bottom of this file.  Nothing
else in the corpus consumes it, and the manuscript's badge sits on the
premise-free `manuscriptNotAmenableOfBaseEmbeds` instead.  The reason it is a
hypothesis rather than a theorem is not difficulty but expressibility, and the
missing vocabulary is itemized below.

**The statement cannot be written down in Lean at all** at the pinned Mathlib
revision (`905b95818eb32af7874a58b427f50c1711a5e96c`).  Nuclearity of a
`C^*`-algebra `A` is the assertion that the identity of `A ⊗_min B` and of
`A ⊗_max B` agree for all `B`, or equivalently that `A` has the completely
positive approximation property.  Every object either definition needs is
missing, and they are named here individually so that a later reader can
re-check the pin rather than trust this paragraph:

1. **The predicate itself.**  A case-insensitive search for "nuclear" over
   Mathlib returns **nothing**.  Over `GroupApproximation/` it returns ten
   files, every hit inside a comment: this module and
   `NuclearityBaseEmbedding`, `PropertyTNonamenable`, `CStarExactness`,
   `ExactnessPermanence`, and the five `CStarTensorProduct*` modules.
2. **`⊗_min`.**  No `C^*`-norm on `A ⊗[ℂ] B` anywhere in Mathlib.  The whole
   of `Mathlib/Analysis/CStarAlgebra/` is ApproximateUnit, Basic, Classes,
   CompletelyPositiveMap, ContinuousFunctionalCalculus/, ContinuousLinearMap,
   ContinuousMap, CStarMatrix, Exponential, Extreme, Fuglede, GelfandDuality,
   GelfandNaimarkSegal, Hom, Matrix, Module/, Multiplier, PositiveLinearMap,
   Projection, SpecialFunctions/, Spectrum, Unitary/, Unitization, lpSpace ---
   there is no `TensorProduct` file among them.
3. **`⊗_max`.**  Worse than absent: there is no universal `C^*`-norm, no
   construction of one, and no roadmap to one anywhere in either library.
   Nuclearity needs the maximal tensor product exactly as much as the minimal
   one, so this alone is decisive.
4. **The completed Hilbert-space tensor product.**
   `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` gives the
   *algebraic* `H ⊗[ℂ] K` its inner product, `TensorProduct.mapL`, and
   `norm_mapL_le`; the completion is not taken there, and
   `Mathlib/Analysis/InnerProductSpace/Completion.lean` is not applied to it.
5. **Stinespring dilation.**  A search for "stinespring" over Mathlib returns
   **nothing**, which closes the completely-positive-approximation route.
6. **The approximation property.**  What Mathlib has is
   `Mathlib/Analysis/CStarAlgebra/CompletelyPositiveMap.lean`: the structure
   `CompletelyPositiveMap` with notation `A₁ →CP A₂`, the class
   `CompletelyPositiveMapClass`, `map_cstarMatrix_nonneg`, and the fact that
   `⋆`-algebra homomorphisms are completely positive.  There is no net, no
   pointwise convergence, and no approximation property built on any of it.
7. **Von Neumann algebras.**  Neither injectivity nor hyperfiniteness exists,
   so Connes' theorem --- the alternative route to the same implication --- is
   not available either.
8. **Group amenability**, which is the *conclusion* Lance delivers, is also
   absent: Mathlib has no `IsAmenable` or `Amenable` predicate at all, and
   `Mathlib/MeasureTheory/Group/FoelnerFilter.lean` says so in its own module
   docstring ("a definition of amenability has not yet been given in
   Mathlib").  Its `IsFoelner.amenable` is not a counterexample: it concludes
   an unbundled invariant finitely additive measure for a group *action* on a
   measure space, not amenability of a discrete group.  That is why both sides
   of Lance's biconditional would have to be phrased in this repository's own
   `Amenability` namespace, and why the hypothesis on
   `reducedGroupCStar_not_nuclear_of_lance` concludes in
   `Amenability.HasInvariantMean`.

Item 3 is worth isolating: even a finished minimal tensor product would leave
nuclearity unstatable.

Beyond Mathlib, this repository has a tensor-product lane of five modules, and
its state must be described carefully.  Only the bottom layer,
`Analysis/CStarTensorProductAdjointable.lean`, is in the import closure of
`GroupApproximation.lean`; it is compiled and audited, and it supplies the
`C^*`-identity `‖T⋆T‖ = ‖T‖²` for adjointable operators on an inner product
space with no completeness assumption.  The four modules above it ---
`Seminorm`, `Spatial`, `Concrete` and the `CStarTensorProduct.lean` entry
point --- are **outside the closure**: nothing has ever compiled them, so
nothing they assert is checked, and the entry point's own claim that this
vocabulary "is machine-checked" is not true today.

Their content, read as mathematics, is the spatial `C^*`-norm attached to a
*chosen* pair of faithful representations, living on the algebraic tensor
product so that no Hilbert-space completion is needed.  That is real and it is
the right construction, but it is three separate steps short of what
nuclearity needs, and no amount of compiling closes the gap: the completion of
the resulting `C^*`-normed `⋆`-algebra is not built, Takesaki's independence of
the norm from `(π, ρ)` is not proved (so the object cannot honestly be called
`⊗_min`), and item 3 above is untouched.  Nuclearity sits above all of it.

Even granting a definition, every published proof of the needed direction
factors through the missing machinery.  The standard route (Brown--Ozawa,
Theorem 2.6.8) runs `C^*_λ(G)` nuclear ⟹ the completely positive
approximation property ⟹ (Stinespring, plus the canonical trace) a net of
finitely supported positive-definite functions on `G` tending to `1`
pointwise ⟹ Reiter's condition ⟹ an invariant mean.  The alternative route
runs through Connes' theorem that injective von Neumann algebras are
hyperfinite, which is heavier still.  Not one leg of either route exists here:
`PropertyTNonamenable` reaches nonamenability by Følner sets and records in
its own docstring that its Reiter/Day route was removed for not compiling, so
even the last leg would have to be written from scratch.

There is no cheaper route for this particular `E`.  The obvious shortcut ---
find a free subgroup of `E` and quote nonnuclearity of `C^*_λ(F_2)` --- buys
nothing even if the free subgroup is produced: nonnuclearity of `C^*_λ(F_2)`
is itself normally deduced from Lance, and transferring it from
`C^*_λ(F_2)` up to `C^*_λ(E)` needs permanence of nuclearity under the
canonical conditional expectation onto a subgroup algebra, which is just as
unformalized.  The structural features of `E` that the manuscript does
formalize (the Clifford sign, the lamp kernel, the compression defect) bear on
MF-ness, not on nuclearity.

## The exact trust surface of the paragraph

The paragraph is split across two declarations, and the split is the point.

`manuscriptNotAmenableOfBaseEmbeds` --- the one the manuscript badges --- states
everything the paragraph asserts up to the last arrow: `\mathcal B → E` is
injective, `\mathcal B` is infinite and Kazhdan, and `E` is nonamenable in both
of the repository's senses.  It has no premises at all.

`reducedGroupCStar_not_nuclear_of_lance` carries the last arrow, with Lance
exposed as an explicit premise rather than tagged, assumed, or hidden behind a
definition.  Because nuclearity has no expressible right-hand side here, the
predicate enters as a quantified parameter; `lance` is then the general
theorem, quantified over all discrete groups, and the conclusion is about `E`
alone, so the premise cannot be discharged by an assumption tailored to `E`.

Two warnings for whoever maintains the conditionality register.  First, a
hypothesised predicate of this shape is **invisible** to
`scripts/check_non_mf_unconditional.py`, whose structural rule keys on
corpus-defined names; the register already records this failure mode for the
`buried-conditional` rows of `MarkovMFConsequences`, and this declaration needs
the same hand-written treatment or the assumption goes unrecorded.  Second,
nothing may badge `reducedGroupCStar_not_nuclear_of_lance` from the manuscript:
it is conditional, and the badge convention is for endpoints that are not.

**Scope note for the reader of the manuscript.**  The nonnuclearity paragraph
is not load-bearing.  Theorem D asserts that `\Cred(E)` is unital, separable,
carries a faithful tracial state, is therefore stably finite, and is not an MF
algebra, and its printed proof (the `proof` environment directly above the
paragraph) invokes only countability of `E`, the faithful-trace lemma, and
Theorem A.  Nonnuclearity is raised only afterwards, to observe that the
example does not settle the *nuclear* form of the Blackadar--Kirchberg
problem.  No theorem of the manuscript depends on it.
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
    have hrw : (fun x : G ↦ k (f g * f x)) = fun x : G ↦ k (f (g * x)) := by
      funext x
      rw [map_mul]
    show m.eval (fun x : G ↦ k (f g * f x)) = m.eval (fun x : G ↦ k (f x))
    rw [hrw]
    exact m.eval_invariant g (fun y : G ↦ k (f y)) hb

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
literal base.**  In the repository's primary amenability predicate: the
property-`(T)` certificate for the base is premise-free, infiniteness is
`infinite_base`, and nonamenability is
`PropertyTNonamenable.infinite_kazhdan_not_isAmenable`. -/
theorem base_not_isAmenable : ¬ IsAmenable LiteralNonMFPresentation.Base := by
  haveI := infinite_base
  exact PropertyTNonamenable.infinite_kazhdan_not_isAmenable
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT

/-- The same in the invariant-mean form, which is the notion Lance's theorem
consumes. -/
theorem base_not_hasInvariantMean :
    ¬ HasInvariantMean LiteralNonMFPresentation.Base :=
  fun h => base_not_isAmenable (isAmenable_of_hasInvariantMean h)

/-- **Every group containing an isomorphic copy of the literal base is
nonamenable.**  The general transport; `markedGroup_not_isAmenable`
instantiates it at `E` along the injectivity of `\mathcal B → E`. -/
theorem not_isAmenable_of_base_embeds {G : Type} [Group G]
    (f : LiteralNonMFPresentation.Base →* G) (hf : Function.Injective f) :
    ¬ IsAmenable G := by
  haveI := infinite_base
  exact PropertyTNonamenable.not_isAmenable_of_infinite_kazhdan_subgroup
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT f hf

/-- The invariant-mean form of the same transport.

An earlier version routed through
`PropertyTNonamenable.not_hasInvariantMean_of_injective`, which does not
exist; it is derived instead from the amenability form beside it.

The universe is `Type`, not `Type*`.  The transport runs through
`not_isAmenable_of_infinite_kazhdan_subgroup`, which places the subgroup and
the ambient group in the *same* universe, and the base lives in `Type`.  The
`Type*` statement was therefore not provable by this route, and stating it
would have promised generality the proof does not deliver. -/
theorem not_hasInvariantMean_of_base_embeds {G : Type} [Group G]
    (f : LiteralNonMFPresentation.Base →* G) (hf : Function.Injective f) :
    ¬ HasInvariantMean G :=
  fun h => not_isAmenable_of_base_embeds f hf (isAmenable_of_hasInvariantMean h)

/-! ## `E` itself -/

/-- **`E` is nonamenable.**  The manuscript's clause "`E` contains an infinite
Kazhdan group and is nonamenable", at the literal forty-one-relator group and
with no hypothesis: the embedding it names is
`NuclearityBaseEmbedding.baseMap_injective`. -/
theorem markedGroup_not_isAmenable :
    ¬ IsAmenable LiteralNonMFPresentation.MarkedGroup :=
  not_isAmenable_of_base_embeds LiteralNonMFPresentation.baseMap
    NuclearityBaseEmbedding.baseMap_injective

/-- The same for the invariant mean on bounded functions, which is the shape
in which Lance's theorem would consume it. -/
theorem markedGroup_not_hasInvariantMean :
    ¬ HasInvariantMean LiteralNonMFPresentation.MarkedGroup :=
  not_hasInvariantMean_of_base_embeds LiteralNonMFPresentation.baseMap
    NuclearityBaseEmbedding.baseMap_injective

/-- **The nonnuclearity paragraph, up to Lance.**  Everything the manuscript
asserts before its final arrow, in one premise-free statement: the canonical
map `\mathcal B → E` is injective, `\mathcal B` is infinite and has property
`(T)`, and `E` is nonamenable in both of the repository's senses.

The manuscript's printed conclusion is this statement together with Lance's
theorem, and with nothing else; see the module docstring for why that theorem
is not expressible at the pinned Mathlib revision and is therefore left in the
prose rather than transcribed here. -/
theorem manuscriptNotAmenableOfBaseEmbeds :
    Function.Injective LiteralNonMFPresentation.baseMap ∧
      Infinite LiteralNonMFPresentation.Base ∧
      HasKazhdanPropertyT.{0, 0} LiteralNonMFPresentation.Base ∧
      ¬ IsAmenable LiteralNonMFPresentation.MarkedGroup ∧
      ¬ HasInvariantMean LiteralNonMFPresentation.MarkedGroup :=
  ⟨NuclearityBaseEmbedding.baseMap_injective, infinite_base,
    LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT,
    markedGroup_not_isAmenable, markedGroup_not_hasInvariantMean⟩

/-! ## The last arrow, with Lance exposed -/

/-- **The manuscript's conclusion, conditional on Lance's theorem.**

`NuclearReduced G` is to be read as the manuscript's "`\Cred(G)` is nuclear",
and `lance` is the one direction of Lance's theorem the manuscript uses:
nuclearity of the reduced algebra of a discrete group forces an invariant mean
on that group.  Given those, `\Cred(E)` fails the predicate --- which is the
paragraph's "whence `\Cred(E)` is not nuclear".

The predicate is a *parameter* rather than a definition, and that is forced,
not stylistic.  Nuclearity is not expressible at the pinned Mathlib revision:
there is no `C^*`-tensor product of either kind and no completely positive
approximation property, so there is no honest right-hand side to give a
`def NuclearReduced`.  Writing one anyway would be a Prop-valued definition
that nothing in the corpus ever establishes, which hides the assumption behind
a name instead of exposing it.  Quantifying over the predicate keeps it
exposed.

The quantifier placement carries the weight.  `lance` ranges over *all*
discrete groups while the conclusion is about `E` alone, so the premise cannot
be satisfied by an assumption cooked up for `E`: it is the general theorem or
nothing.  What is proved here is therefore exactly the paragraph's final
arrow, and nothing about nuclearity itself.

The mathematical content on this side of the arrow is
`markedGroup_not_hasInvariantMean`, which is premise-free. -/
theorem reducedGroupCStar_not_nuclear_of_lance
    (NuclearReduced : ∀ (G : Type) [Group G], Prop)
    (lance : ∀ (G : Type) [Group G],
      NuclearReduced G → HasInvariantMean G) :
    ¬ NuclearReduced LiteralNonMFPresentation.MarkedGroup :=
  fun hn => markedGroup_not_hasInvariantMean
    (lance LiteralNonMFPresentation.MarkedGroup hn)

end NuclearityAmenability
end GroupApproximation
