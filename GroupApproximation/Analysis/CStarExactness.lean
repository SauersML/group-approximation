import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Exactness of C⋆-algebras: the part of the vocabulary that is actually definable

## The manuscript claim

`non_mf_groups_exist.tex`, the paragraph opened by
`\paragraph{An exact stably finite non-MF algebra.}` --- located by that
string, since line numbers drift --- asserts:

> The same witness gives a concrete separable exact example: `Cred(W)` is exact,
> has a faithful tracial state, is stably finite, and is not MF.  Indeed, the
> locally finite lamp kernel is amenable and hence exact, while the linear group
> `V ≤ GL₄(ℚ)` is exact [GHW].  Exact groups are closed under extensions
> [KWPermanence], so `W` is exact; for discrete groups this is equivalent to
> exactness of the reduced group algebra [KWExact].  [...]  All parts of this
> paragraph except exactness are also verified in Lean; the present formal
> library has no definition of exact C⋆-algebras.

So the manuscript does **not** prove exactness of the algebra.  It cites a chain
of four external theorems, numbered `E.1`--`E.4` throughout this development:

* **E.1** a locally finite group is amenable, and amenable groups are exact
  (folklore; the manuscript gives no citation);
* **E.2** a finitely generated linear group over a field is exact --- applied
  to `V ≤ GL₄(ℚ)` (`\cite{GHW}`, Guentner--Higson--Weinberger, *The Novikov
  conjecture for linear groups*, Publ. IHES 101 (2005));
* **E.3** exactness of groups is closed under extensions, giving `W` exact
  (`\cite{KWPermanence}`, Kirchberg--Wassermann, *Permanence properties of
  C⋆-exact groups*, Doc. Math. 4 (1999));
* **E.4** for a discrete group `G`, `G` is exact iff `Cred(G)` is exact
  (`\cite{KWExact}`, Kirchberg--Wassermann, *Exact groups and continuous
  bundles of C⋆-algebras*, Math. Ann. 315 (1999)).

**The decisive structural point** is that `E.1`--`E.3` are statements about
exactness *of groups*, which is Yu's property A and is purely combinatorial;
only `E.4` crosses over to the C⋆-algebra and therefore only `E.4` needs the
tensor-product theory that Mathlib does not have.  The group side is developed
in `ExactnessPermanence.lean` and `PropertyAExtension.lean`; this file is the
C⋆ side.

**Where the group side now stands.**  `E.1` is proved on the manuscript's own
lamp group (`ExactnessPermanence.hasPropertyA_cliffordLamp_viaAmenability`:
locally finite `⟹` amenable `⟹` property A).  `E.3` is proved in full
(`PropertyAExtension.hasPropertyA_of_ker_of_quotient`), together with the
semidirect-product form the manuscript actually uses
(`PropertyAExtension.hasPropertyA_semidirectProduct_of_isLocallyFiniteGroup`).
So of the two group-side links that were open, one is closed outright and the
other, `E.2`, is Guentner--Higson--Weinberger's theorem, which this repository
does not prove and does not transcribe: the semidirect-product corollary takes
property A of the quotient as an explicit hypothesis, so the conditionality is
visible in its type.

That leaves `E.4` as the sole *structural* obstruction, and it is the one this
file is about.

## What Mathlib has, and what it does not

Surveyed against the pinned revision (`lake-manifest.json`, mathlib
`905b95818eb32af7874a58b427f50c1711a5e96c`, tag `v4.32.2`), twice and
independently: once against a local clone holding that exact commit, and once
against the remote build node.  Both agree.

The gap is **not** that Mathlib has nothing.  It is that Mathlib has all of the
algebraic and Hilbertian scaffolding and **no C⋆-norms on a tensor product**.

*Present* (the scaffolding, more of it than one might expect):

* `Mathlib/Algebra/Star/TensorProduct.lean`: `Star`, `InvolutiveStar`,
  `StarAddMonoid`, `StarModule` on `A ⊗[R] B`, with
  `@[simp] star_tmul : star (x ⊗ₜ y) = star x ⊗ₜ star y := rfl`.
* `Mathlib/RingTheory/TensorProduct/Basic.lean`: `instAlgebra : Algebra R
  (A ⊗[R] B)` (:298), and `StarMul`/`StarRing (A ⊗[R] B)` (:747--756).  So the
  algebraic tensor product is already a ⋆-algebra.
* `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`: `instInner`,
  `inner_tmul`, `instNormedAddCommGroup` (:133) and
  `instInnerProductSpace : InnerProductSpace 𝕜 (E ⊗[𝕜] F)` (:144) --- with **no**
  finite-dimensionality hypothesis --- plus `@[simp] norm_tmul : ‖x ⊗ₜ y‖ =
  ‖x‖ * ‖y‖` (:146), i.e. the Hilbert cross norm is already multiplicative on
  elementary tensors.  It also has the *operator* tensor:
  `ContinuousLinearMap.mapL` (:556) with `norm_mapL_le : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖`
  (:559), `mapL_mul` (:605), `mapL_comp`, `rTensor`/`lTensor` and their `_mul`
  and `_comp` laws, and `mapIsometry`, `congrIsometry`, `commIsometry`,
  `assocIsometry`, `Orthonormal.tmul`.
* `Mathlib/Analysis/InnerProductSpace/Completion.lean`:
  `Completion.innerProductSpace : InnerProductSpace 𝕜 (Completion E)` (:89).
* `Mathlib/Analysis/CStarAlgebra/CompletelyPositiveMap.lean` and
  `PositiveLinearMap.lean`: completely positive and positive linear maps.

*Absent*, and this is the whole obstruction:

* **C⋆-norms on a tensor product.**  No file under
  `Mathlib/Analysis/CStarAlgebra/` so much as mentions `⊗`.  There is no
  spatial/minimal completion, no maximal C⋆-norm, and no theory of either.
* **Nuclearity.**  `grep -rli nuclear Mathlib/` returns nothing at all.
* **Exactness**, which is defined in terms of the minimal tensor product and is
  therefore not even statable.
* **Quotient C⋆-algebras.**  `Mathlib/Analysis/Normed/Group/Quotient.lean` has
  `Ideal.Quotient.semiNormedCommRing` (:495) and `normedCommRing` (:512), both
  *commutative only*; nothing makes `B ⧸ J` a C⋆-algebra.
* Amenability of groups, and the Gelfand--Naimark faithful representation
  theorem.

*Present and used in this file*: `CStarMatrix` with its ring/star structure,
`CStarMatrix.mapₙₐ`, the C⋆-algebra classes, `NonUnitalStarAlgHom.norm_map`
(injective ⋆-homomorphisms of C⋆-algebras are isometric), and
`CStarAlgebra (E →L[ℂ] E)`.  Mathlib's *bundled* `A →CP B` is **not** used: it
is stated with `[PartialOrder A] [StarOrderedRing A]` side instances that the
concrete algebras of this repository (closed `StarSubalgebra`s of `B(ℓ²G)`) do
not carry, so complete positivity is respelled below in the equivalent
unbundled `∃ N, M = star N * N` form.

## Consequence for the definition of exactness

The textbook definition of exactness --- `A` is exact when
`A ⊗_min ·` carries short exact sequences to short exact sequences --- is *not
expressible* in this library, because neither `⊗_min` nor the quotient
C⋆-algebra `B/J` exists.  This is what blocks link `E.4`.  Given the scaffolding
listed above, what has to be built is narrower than "the whole theory": the
completion `Completion (H ⊗[ℂ] K)` assembled into a Hilbert space tensor
product, the continuous extension of `mapL` to it, the resulting operator norm
recognised as a C⋆-norm, and then Takesaki's independence-of-representation
theorem.  Those constructions are owned by the peer modules
`Analysis/CStarTensorProduct*.lean` (minimal/spatial), and by the queued
maximal-norm and nuclearity modules; nothing here duplicates them.  `E.4`
depends on their output.

What *is* expressible is Kirchberg's characterisation: a separable C⋆-algebra is
exact if and only if it is **nuclearly embeddable**, i.e. admits a faithful
⋆-homomorphism into a C⋆-algebra which is a nuclear map (point-norm
approximable by completely positive contractions factoring through
finite-dimensional C⋆-algebras).  That is the notion defined here, under the
name `IsNuclearlyEmbeddable`, deliberately *not* under the name `IsExact`:

* the equivalence `exact ↔ nuclearly embeddable` is Kirchberg's theorem and is
  **not** formalized here;
* nothing in this file, or anywhere in the repository, proves or assumes that
  `Cred(W)` --- or any nonnuclear algebra at all --- is nuclearly embeddable.

The manuscript's exactness row therefore remains **MISSING**, and this file
makes the missing statement precise rather than pretending to close it.  The
definition below is a genuine definition with genuine content: dropping the
finite-dimensionality of the approximant `D` would make every completely
positive map nuclear (take `D = A`, `α = id`, `β = φ`), so the
finite-dimensionality hypothesis is what carries the mathematics.

**Exactly what is missing, as of the group side being closed.**  Two things,
and they are of different kinds.

1. `E.2`, property A for finitely generated linear groups.  A *theorem*, not a
   vocabulary gap: it is statable today, and stating it is what
   `PropertyAExtension.hasPropertyA_semidirectProduct_of_isLocallyFiniteGroup`
   does by taking it as a hypothesis.  Proving it means formalizing
   Guentner--Higson--Weinberger --- actions on products of affine buildings over
   the completions of a finitely generated field --- and is research-scale.
2. `E.4`, the crossover.  A *vocabulary* gap, and the shortfall is now
   itemised rather than global, because the peer C⋆-tensor lane has moved.
   What that lane has built is the spatial C⋆-norm **relative to a fixed pair
   of faithful representations** (`CStarTensorProductSpatial.lean`,
   `CStarTensorProductConcrete.lean`, including the cross-norm property).  What
   is still absent, at the pinned Mathlib revision and in this repository:
   * canonicity of that norm --- Takesaki's independence-of-representation
     theorem --- without which there is no `⊗_min`, only `⊗_{π,ρ}`;
   * the completion of a C⋆-normed ⋆-algebra to a C⋆-algebra (Stage B of the
     tensor lane's roadmap), so `A ⊗_{π,ρ} B` is not yet an algebra;
   * a C⋆-algebra structure on a quotient `B ⧸ J` by a closed two-sided ideal
     --- Mathlib's `Ideal.Quotient.semiNormedCommRing` is commutative only, and
     nothing in this repository supplies the noncommutative case;
   * consequently, no predicate `IsExact` for C⋆-algebras anywhere;
   * and, for the group-to-algebra passage itself, no crossed products and no
     uniform Roe algebra, which is what Ozawa's proof of
     `property A ⟹ Cred(G) exact` runs through.

So the shape of the residual obligation is now sharp: supply `⊗_min` and the
C⋆-quotient, define `IsExact`, and the manuscript's sentence becomes a
statement; supply Ozawa and `E.2`, and it becomes a theorem.  Neither is
attempted here, and no declaration in this file or in `PropertyAExtension.lean`
asserts, assumes, or names any of them.

## The exactness row: the standing record of what would close it

This section is the durable statement of the gap.  It is written so that a
later reader need consult no report, no commit message and no other module.

**What the Lean chain actually is, against what the manuscript prints.**  The
manuscript's chain is

```
    amenable ⟹ exact  →  linear ⟹ exact  →  extension of exacts is exact
        ⟹ Cred(W) exact .
```

What this repository contains is

```
    locally finite ⟹ amenable ⟹ property A  →  (hypothesis: property A of Σ)
        →  extension of property-A groups has property A .
```

The second chain is complete and machine-checked at its own level
(`ExactnessPermanence.lean`, `PropertyAExtension.lean`).  It does **not** reach
the first, and the two are joined by exactly two unformalized theorems.

**Missing theorem 1 --- Ozawa / Higson--Roe.**  For a countable discrete group,
`property A ⟺ Cred(G) is exact`.  This is the identification that lets the
combinatorial chain stand in for the printed one.  It is **neither proved nor
assumed** here: no declaration anywhere in this repository converts a
`HasPropertyA` conclusion into an exactness conclusion, and none could, because
there is no exactness predicate to convert into.  Property A is therefore a
*substitute notion*, and the substitution is unjustified in the formal
development --- deliberately, and visibly.

**Missing theorem 2 --- Guentner--Higson--Weinberger.**  A finitely generated
linear group has property A, applied to `Σ ≤ GL₄(ℚ)`.  Statable today; entered
as the explicit hypothesis `HasPropertyA H` of
`PropertyAExtension.hasPropertyA_semidirectProduct_of_isLocallyFiniteGroup`,
never as a named transcription (the `LITERATURE_INPUT` roster in
`scripts/Audit.lean` is deliberately empty and this development adds nothing to
it).

**Missing Mathlib objects.**  Even granting both theorems, the conclusion is
not *statable*.  Three objects are absent at the pinned revision:

1. **A canonical minimal tensor product `⊗_min`.**  The repository's
   `Analysis/CStarTensorProduct*` lane builds the spatial C⋆-seminorm relative
   to a *chosen* pair of faithful representations, and proves the cross-norm
   property.  What is missing is Takesaki's independence-of-representation
   theorem; without it the norm is `‖·‖_{π,ρ}` and cannot honestly be written
   `‖·‖_min`.  That theorem genuinely needs states, GNS and continuous slice
   maps.
2. **A C⋆-algebra structure on a quotient `B ⧸ J` by a closed two-sided
   ideal.**  Mathlib's `Ideal.Quotient.semiNormedCommRing` and `normedCommRing`
   (`Analysis/Normed/Group/Quotient.lean:495,512`) are **commutative only**, so
   even the seminormed quotient *ring* must be redone noncommutatively before
   the C⋆-identity on the quotient can be approached.
3. **Consequently no predicate `IsExact` for C⋆-algebras**, anywhere --- since
   exactness is defined by `A ⊗_min ·` carrying short exact sequences to short
   exact sequences, and (1) and (2) are both prerequisites for writing that
   down.  `grep -rli nuclear` over Mathlib at this revision returns nothing at
   all.

For Ozawa's route in particular, crossed products and the uniform Roe algebra
are also absent, and Mathlib has no crossed products of any kind.

**Where the tensor lane's formerly-undischarged hypothesis sits in this.**
`CStarTensorProductSpatial.spatialNorm_isCStarNorm_of_injective` assumed
`Function.Injective (spatialHom π ρ)`.  That hypothesis is **now proved**
(`CStarTensorProductSpatial.spatialHom_injective`), by a purely algebraic
argument --- the vector functionals separate points, plus a Hamel basis on one
factor --- with no states, no GNS and no continuity.  The unconditional
consequence is `spatialNorm_isCStarNorm`.

**This must not be mistaken for progress on this row, and the temptation is
real, so it is worth saying flatly.**  What was upgraded is a *conditional*
C⋆-norm to an unconditional one **for a fixed pair `(π, ρ)`**.  It says nothing
about canonicity.  Item (1) above --- Takesaki's independence theorem, which is
what would let the norm be written `‖·‖_min` at all --- stands entirely
untouched, and item (2), the noncommutative C⋆-quotient, is untouched as well.
`IsExact` therefore remains unstatable, and the exactness row is exactly as
missing as it was before.

**Therefore the manuscript's exactness row is MISSING**, and the manuscript's
own sentence --- *"the present formal library has no definition of exact
C⋆-algebras"* --- is the accurate description.  No `\leanverified` badge points
at any declaration in this file, in `ExactnessPermanence.lean`, in
`PropertyAExtension.lean`, or in the `CStarTensorProduct*` lane.

## Contents

* `IsCStarShortExact` --- a short exact sequence of C⋆-algebras.
* `IsCompletelyPositive` --- unbundled complete positivity of a `ℂ`-linear map.
* `FinDimCStarAlgebra` --- a bundled finite-dimensional complex C⋆-algebra.
* `IsNuclearMap`, `IsNuclearCStarAlgebra`, `IsNuclearlyEmbeddable`.
* Permanence that is genuinely provable at this level: complete positivity is
  closed under composition and contains ⋆-homomorphisms; nuclearity of a map is
  stable under precomposition with an injective ⋆-homomorphism; hence nuclear
  embeddability passes to C⋆-subalgebras.

## Coordination

`IsNuclearCStarAlgebra` here is the *completely positive approximation
property* --- the identity map is point-norm approximable by CP contractions
through finite-dimensional C⋆-algebras.  A separate nuclearity module built on
the minimal tensor product will define nuclearity as `‖·‖_min = ‖·‖_max`.  The
two agree (Choi--Effros/Kirchberg), but that agreement is a theorem, not a
definition, so the two notions must not be silently identified when the tensor
modules land.  Whichever name survives, the equivalence is a row that has to be
proved.
-/

namespace GroupApproximation
namespace CStarExactness

universe u v w

/-! ## Short exact sequences of C⋆-algebras

This is the shape of the statement `0 → A ⊗ J → A ⊗ B → A ⊗ (B/J) → 0` whose
exactness *defines* exactness of `A`.  Recorded so that the missing content is
exactly one construction (the tensor product) rather than a whole vocabulary.
-/

/-- A short exact sequence `0 → J → B → Q → 0` of complex C⋆-algebras: `f` is
injective, `g` is surjective, and the kernel of `g` is precisely the range of
`f`. -/
structure IsCStarShortExact {J : Type u} {B : Type v} {Q : Type w}
    [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra Q]
    (f : J →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] Q) : Prop where
  /-- The inclusion of the ideal is injective. -/
  injective : Function.Injective f
  /-- The quotient map is surjective. -/
  surjective : Function.Surjective g
  /-- Exactness in the middle: the kernel of `g` is the range of `f`. -/
  exact_middle : ∀ b : B, g b = 0 ↔ ∃ j : J, f j = b

/-- In a short exact sequence the composite of the two maps vanishes. -/
theorem IsCStarShortExact.comp_eq_zero {J : Type u} {B : Type v} {Q : Type w}
    [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra Q]
    {f : J →⋆ₙₐ[ℂ] B} {g : B →⋆ₙₐ[ℂ] Q} (h : IsCStarShortExact f g) (j : J) :
    g (f j) = 0 :=
  (h.exact_middle (f j)).mpr ⟨j, rfl⟩

/-! ## Complete positivity

In a C⋆-algebra the positive cone is exactly `{star y * y}`, and `Mₙ(A)` with
its C⋆-norm is again a C⋆-algebra, so the following is the standard notion of a
completely positive map.  It is stated without any order instance so that it
applies verbatim to closed `StarSubalgebra`s of `B(H)`, which is the shape in
which every concrete algebra of this repository appears.
-/

/-- A `ℂ`-linear map between C⋆-algebras is **completely positive** when, for
every `n`, applying it entrywise sends positive `n × n` matrices over the source
to positive `n × n` matrices over the target.  Positivity is spelled in the
equivalent form `M = star N * N`, which needs no order instance. -/
def IsCompletelyPositive {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (φ : A →ₗ[ℂ] B) : Prop :=
  ∀ (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) A),
    (∃ N : CStarMatrix (Fin n) (Fin n) A, M = star N * N) →
      ∃ P : CStarMatrix (Fin n) (Fin n) B, M.map ⇑φ = star P * P

/-- The identity map is completely positive. -/
theorem isCompletelyPositive_id {A : Type u} [NonUnitalCStarAlgebra A] :
    IsCompletelyPositive (LinearMap.id : A →ₗ[ℂ] A) := by
  intro n M hM
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, ?_⟩
  have h : M.map ⇑(LinearMap.id : A →ₗ[ℂ] A) = M := by
    ext i j
    rfl
  rw [h]
  exact hN

/-- Completely positive maps are closed under composition. -/
theorem IsCompletelyPositive.comp {A : Type u} {B : Type v} {C : Type w}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    {φ : A →ₗ[ℂ] B} {ψ : B →ₗ[ℂ] C}
    (hψ : IsCompletelyPositive ψ) (hφ : IsCompletelyPositive φ) :
    IsCompletelyPositive (ψ ∘ₗ φ) := by
  intro n M hM
  obtain ⟨P, hP⟩ := hφ n M hM
  obtain ⟨Q, hQ⟩ := hψ n (M.map ⇑φ) ⟨P, hP⟩
  refine ⟨Q, ?_⟩
  have h : M.map ⇑(ψ ∘ₗ φ) = (M.map ⇑φ).map ⇑ψ := by
    ext i j
    rfl
  rw [h]
  exact hQ

/-- A non-unital ⋆-homomorphism of C⋆-algebras is completely positive: applying
it entrywise is again a ⋆-homomorphism on matrices, so it carries `star N * N`
to `star (N.map f) * (N.map f)`. -/
theorem isCompletelyPositive_of_starAlgHom {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (f : A →⋆ₙₐ[ℂ] B) :
    IsCompletelyPositive ((f : A →ₗ[ℂ] B)) := by
  intro n M hM
  obtain ⟨N, hN⟩ := hM
  refine ⟨CStarMatrix.mapₙₐ (n := Fin n) f N, ?_⟩
  have h : M.map ⇑(f : A →ₗ[ℂ] B) = CStarMatrix.mapₙₐ (n := Fin n) f M := by
    ext i j
    rfl
  rw [h, hN, map_mul, map_star]

/-! ## Finite-dimensional approximants -/

/-- A finite-dimensional complex C⋆-algebra, bundled with its instances.  Every
such algebra is a finite direct sum of matrix algebras, so nothing is lost by
placing the carrier in `Type`; bundling keeps the universe of the approximant
independent of the universes of the algebras being approximated, which is what
makes `IsNuclearMap` composable. -/
structure FinDimCStarAlgebra where
  /-- The underlying type. -/
  carrier : Type
  [algebra : CStarAlgebra carrier]
  [findim : FiniteDimensional ℂ carrier]

attribute [instance] FinDimCStarAlgebra.algebra FinDimCStarAlgebra.findim

instance finDimCStarAlgebraCoeSort : CoeSort FinDimCStarAlgebra Type :=
  ⟨FinDimCStarAlgebra.carrier⟩

/-! ## Nuclear maps and nuclear embeddability -/

/-- A `ℂ`-linear map between C⋆-algebras is a **nuclear map** when it is
point-norm approximable, uniformly on finite subsets, by composites
`β ∘ α` of completely positive contractions through a finite-dimensional
C⋆-algebra.

Finite-dimensionality of `D` is the whole content: without it one could take
`D = A`, `α = id`, `β = φ`. -/
def IsNuclearMap {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (φ : A →ₗ[ℂ] B) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (D : FinDimCStarAlgebra) (α : A →ₗ[ℂ] D) (β : D →ₗ[ℂ] B),
      IsCompletelyPositive α ∧ IsCompletelyPositive β ∧
        (∀ a : A, ‖α a‖ ≤ ‖a‖) ∧ (∀ d : D, ‖β d‖ ≤ ‖d‖) ∧
          ∀ a ∈ F, ‖β (α a) - φ a‖ ≤ ε

/-- A C⋆-algebra is **nuclear** when its identity map is a nuclear map, i.e.
when it has the completely positive approximation property. -/
def IsNuclearCStarAlgebra (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  IsNuclearMap (LinearMap.id : A →ₗ[ℂ] A)

/-- A complex C⋆-algebra bundled with its instance.  Used only so that
"there exists a C⋆-algebra such that ..." needs no instance binder inside an
existential. -/
structure CStarAlgebraBundle where
  /-- The underlying type. -/
  carrier : Type u
  [algebra : NonUnitalCStarAlgebra carrier]

attribute [instance] CStarAlgebraBundle.algebra

instance cStarAlgebraBundleCoeSort : CoeSort CStarAlgebraBundle.{u} (Type u) :=
  ⟨CStarAlgebraBundle.carrier⟩

/-- A C⋆-algebra is **nuclearly embeddable** when it admits a faithful
⋆-homomorphism into some C⋆-algebra which is a nuclear map.

By Kirchberg's theorem this is equivalent, for separable algebras, to
exactness; and by Gelfand--Naimark it is equivalent to the textbook form in
which the target is required to be `B(H)`.  Neither equivalence is formalized:
this is a *definition*, and the name deliberately avoids the word `exact`.

**Do not badge the manuscript's exactness sentence with this predicate.**  It
is the most inviting mistake available in this lane, because unlike `IsExact`
this predicate *is* definable today, so a future reader will find a statable
proxy sitting where the unstatable claim should be.  Proving
`IsNuclearlyEmbeddable (Cred W)` would not establish what the manuscript
prints: the bridge between the two is Kirchberg's theorem, which is not
proved here, so a badge pointing at it would certify a true statement that is
not the printed one --- the exact defect class this development exists to
catch.  The manuscript's claim needs `IsExact`, and `IsExact` needs `⊗_min`
and a noncommutative C⋆-quotient; see the standing record above. -/
def IsNuclearlyEmbeddable (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∃ (B : CStarAlgebraBundle.{u}) (π : A →⋆ₙₐ[ℂ] B),
    Function.Injective π ∧ IsNuclearMap ((π : A →ₗ[ℂ] B))

/-! ## Permanence that is genuinely reachable

Exactness passes to C⋆-subalgebras.  Under the nuclear-embeddability
formulation this is not a deep theorem, and it is proved here in full: an
injective ⋆-homomorphism of C⋆-algebras is isometric, so precomposing a
completely positive contraction with it again gives a completely positive
contraction, and the approximation is tested on the image of the finite set.
-/

/-- Nuclearity of a map is stable under precomposition with an injective
⋆-homomorphism. -/
theorem IsNuclearMap.comp_injective_starAlgHom
    {A : Type u} {B : Type v} {C : Type w}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    {φ : B →ₗ[ℂ] C} (hφ : IsNuclearMap φ)
    (ι : A →⋆ₙₐ[ℂ] B) (hι : Function.Injective ι) :
    IsNuclearMap (φ ∘ₗ (ι : A →ₗ[ℂ] B)) := by
  classical
  intro F ε hε
  obtain ⟨D, α, β, hα, hβ, hαc, hβc, happ⟩ :=
    hφ (F.image (fun a : A ↦ (ι a : B))) ε hε
  refine ⟨D, α ∘ₗ (ι : A →ₗ[ℂ] B), β,
    hα.comp (isCompletelyPositive_of_starAlgHom ι), hβ, ?_, hβc, ?_⟩
  · intro a
    have hnorm : ‖(ι a : B)‖ = ‖a‖ := NonUnitalStarAlgHom.norm_map ι hι a
    have hle : ‖α (ι a)‖ ≤ ‖(ι a : B)‖ := hαc (ι a)
    calc ‖(α ∘ₗ (ι : A →ₗ[ℂ] B)) a‖ = ‖α (ι a)‖ := rfl
      _ ≤ ‖(ι a : B)‖ := hle
      _ = ‖a‖ := hnorm
  · intro a ha
    exact happ (ι a) (Finset.mem_image_of_mem _ ha)

/-- **Nuclear embeddability passes to C⋆-subalgebras**, in the form: it is
inherited along any injective ⋆-homomorphism.  (Source and target are taken in
the same universe because the witnessing algebra produced for the target is
reused for the source.) -/
theorem IsNuclearlyEmbeddable.of_injective_starAlgHom
    {A : Type u} {B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (ι : A →⋆ₙₐ[ℂ] B) (hι : Function.Injective ι) (hB : IsNuclearlyEmbeddable B) :
    IsNuclearlyEmbeddable A := by
  obtain ⟨C, π, hπ, hnuc⟩ := hB
  have hinj : Function.Injective ⇑(π.comp ι) := by
    rw [NonUnitalStarAlgHom.coe_comp]
    exact hπ.comp hι
  refine ⟨C, π.comp ι, hinj, ?_⟩
  exact hnuc.comp_injective_starAlgHom ι hι

/-- A nuclear C⋆-algebra is nuclearly embeddable: the identity ⋆-homomorphism
is a faithful nuclear embedding of the algebra into itself. -/
theorem IsNuclearCStarAlgebra.isNuclearlyEmbeddable {A : Type u}
    [NonUnitalCStarAlgebra A] (hA : IsNuclearCStarAlgebra A) :
    IsNuclearlyEmbeddable A := by
  refine ⟨⟨A⟩, NonUnitalStarAlgHom.id ℂ A, fun _ _ h ↦ h, ?_⟩
  intro F ε hε
  obtain ⟨D, α, β, hα, hβ, hαc, hβc, happ⟩ := hA F ε hε
  exact ⟨D, α, β, hα, hβ, hαc, hβc, happ⟩

/-- The scalars are a nuclear C⋆-algebra: the identity already factors through
the finite-dimensional algebra `ℂ`.  Recorded so that `IsNuclearMap` is visibly
satisfiable and the definition is not vacuous. -/
theorem isNuclearCStarAlgebra_complex : IsNuclearCStarAlgebra ℂ := by
  intro _F ε hε
  refine ⟨⟨ℂ⟩, LinearMap.id, LinearMap.id, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCompletelyPositive_id
  · exact isCompletelyPositive_id
  · intro a
    exact le_rfl
  · intro d
    exact le_rfl
  · intro a _
    simpa using hε.le

end CStarExactness
end GroupApproximation
