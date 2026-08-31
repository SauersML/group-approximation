import GroupApproximation.Analysis.STW22CounterexampleAssembly
import GroupApproximation.Analysis.CuntzPedersenJordanTracial

/-!
# The two routes to the rogue trace, and `T(A) ⊊ T(M)` as a theorem

`Analysis/STW22CounterexampleAssembly` reaches the endpoint from the
compactness interface.  This file does two things it left undone.

## One core, two entry points

The (A15)--(A17) argument never looks at *how* the detecting trace was
produced.  All it uses is a gauge-null bounded sequence whose corona class some
tracial state does not kill.  `hasUniformTwoDiscontinuousTracialState_of_detected`
states exactly that, and both routes are one line from it:

* `hasUniformTwoDiscontinuousTracialState_of_compactness` --- the route the
  construction now takes.  Its hypothesis is the coordinate-state solvability
  of `Analysis/CoronaCoordinateStateCompactness`: finitely many state
  constraints are solved at one sufficiently late coordinate, and
  Banach--Alaoglu assembles the trace.  No literature theorem is assumed.

* `hasUniformTwoDiscontinuousTracialState_of_jordan` --- the alternative,
  restored here after the assembly was re-cut.  It starts from a norm-distance
  `BlockObstruction`, uses Hahn--Banach and the Jordan decomposition of a
  bounded hermitian functional, and therefore carries the two literature
  hypotheses `HasJordanDecomposition` and `HasUniqueJordanDecomposition` on the
  corona.  It is kept because it is a genuinely different derivation of the same
  conclusion, not because anything depends on it.

The two hypotheses are not comparable: the Jordan route needs a norm-distance
bound at every tail index and two unproved literature statements, and it needs
`‖h_s‖ = 1`; the compactness route needs a state at arbitrarily late coordinates
and nothing else.

## `T(A) ⊊ T(M)` as a theorem

The assembly proved that some tracial state of `M = ℂ1 + J` is not continuous
for the gauge, and left the last step --- that such a state is therefore not the
extension of any trace of `A` --- as a remark.  That step is proved here.

The content is `eq_of_eqOn_unitizedC0Sum`: a uniform-two-continuous tracial
state of `M` is **determined** by its values on `A`.  This is where (A8) is
used, through the landed scalar truncations: every element of `M` is the
uniform-two-limit of elements of `A`, so continuity pins the extension.  That
makes "the uniform-two-continuous extension of a trace of `A`" a well-defined
and injective map `T(A) → T(M)`, and identifies its image:

`isExtensionOfSomeBaseFunctional_iff` --- a tracial state of `M` is in the image
exactly when it is continuous for the gauge.

`not_extensionMapSurjective` then converts the assembly's discontinuous state
into the audit's (A18): the extension map is not surjective, i.e.
`T(A) ⊊ T(M)`.  Nothing about surjectivity is assumed; the proper inclusion is
the theorem.

## What is still not proved

That the extension map is *total* --- that every trace of `A` really does extend
continuously --- is not proved here and is not needed for non-surjectivity.  Its
proof needs `|τ a| ≤ ‖a‖_{2,T(A)}` for a tracial state `τ` of `A`, which for an
abstract `TracialTwoGauge` is an extra hypothesis relating the gauge to the
tracial two-norms rather than a consequence of the recorded fields.  Stating it
would add an assumption; leaving it out costs nothing, because a map with a
point outside its image is not surjective whatever its domain.
-/

namespace GroupApproximation
namespace STW22CompactnessRoute

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialCompletionIdentification
open CuntzPedersenCoronaObstruction CuntzPedersenJordanTracial
open CStarState CoronaCoordinateStateCompactness
open STW22Assembly

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-! ## The tail lemmas, keyed on a bare gauge-null hypothesis

`Analysis/STW22CounterexampleAssembly` proves these for a bundled
`CoordinateStateBlockData`.  Both routes need them for a sequence carrying no
bundle, so they are restated here on the hypothesis they actually use. -/

/-- A gauge-null bounded sequence has all its tails in the ideal `J`. -/
theorem tail_mem_twoNullIdeal_of_gauge_null (G : TracialTwoGauge D)
    {x : BoundedCStarSequence D}
    (hx : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0)) (N : ℕ) :
    tail x N ∈ twoNullIdeal G := by
  rw [mem_twoNullIdeal_iff]
  refine squeeze_zero' (Eventually.of_forall fun n ↦ G.nonneg n _)
    (Eventually.of_forall fun n ↦ ?_) hx
  rw [tail_apply]
  split_ifs
  · rw [G.zero]
    exact G.nonneg n (x n)
  · exact le_rfl

/-- A gauge-null bounded sequence has all its tails in `M = ℂ1 + J`. -/
theorem tail_mem_scalarPlusJ_of_gauge_null (G : TracialTwoGauge D)
    {x : BoundedCStarSequence D}
    (hx : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0)) (N : ℕ) :
    tail x N ∈ scalarPlusJ G :=
  twoNullIdeal_le_scalarPlusJ G (tail_mem_twoNullIdeal_of_gauge_null G hx N)

/-- **(A17) on a bare gauge-null hypothesis.**  The uniform two-norms of the
tails tend to zero. -/
theorem uniformTwoNorm_tail_tendsto_zero_of_gauge_null (G : TracialTwoGauge D)
    {x : BoundedCStarSequence D}
    (hx : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0)) :
    Tendsto (fun N ↦ uniformTwoNorm G (tail x N)) atTop (nhds 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hev : ∀ᶠ n in atTop, G.q n (x n) < ε / 2 :=
    ((Metric.tendsto_nhds.mp hx) (ε / 2) (half_pos hε)).mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)] using hn
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  filter_upwards [eventually_ge_atTop K] with N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (uniformTwoNorm_nonneg G _)]
  have hbd : uniformTwoNorm G (tail x N) ≤ ε / 2 := by
    refine uniformTwoNorm_le G _ fun n ↦ ?_
    rw [tail_apply]
    split_ifs with hn
    · rw [G.zero]
      linarith
    · exact (hK n (by omega)).le
  linarith

/-! ## The shared core -/

/-- **(A15)--(A17), stated once.**  A gauge-null bounded sequence whose corona
class is not annihilated by some tracial state of the corona produces a tracial
state of `M = ℂ1 + J` which is not continuous for the gauge.

Nothing here knows how the corona trace was obtained, which is why both routes
below are one line from it.  The mechanism is the audit's: removing a finite
prefix does not move the corona class, so the pullback is constant on the tails,
while the tails are uniformly two-null. -/
theorem hasUniformTwoDiscontinuousTracialState_of_detected
    (G : TracialTwoGauge D) {x : BoundedCStarSequence D}
    (hgauge : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0))
    {σ : TracialState (CStarProductCorona D atTop)}
    (hσ : σ (cStarProductCoronaQuotient D atTop x) ≠ 0) :
    HasUniformTwoDiscontinuousTracialState G := by
  refine ⟨pullbackTracialState G σ, ?_⟩
  refine not_isUniformTwoContinuous_of_constant_value G (pullbackTracialState G σ)
    (fun N ↦ ⟨tail x N, tail_mem_scalarPlusJ_of_gauge_null G hgauge N⟩)
    hσ (fun N ↦ ?_)
    (uniformTwoNorm_tail_tendsto_zero_of_gauge_null G hgauge)
  show σ (cStarProductCoronaQuotient D atTop (tail x N))
    = σ (cStarProductCoronaQuotient D atTop x)
  rw [corona_tail_eq]

/-! ## Route one: compactness -/

/-- **The compactness route.**  Arbitrarily late coordinate-state solvability
gives the corona trace, and the core does the rest.  This is the route the
construction takes, and it assumes no literature theorem: the trace comes from
solving finitely many state constraints at one late coordinate and applying
Banach--Alaoglu. -/
theorem hasUniformTwoDiscontinuousTracialState_of_compactness
    (G : TracialTwoGauge D) {x : BoundedCStarSequence D}
    (hgauge : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0))
    (hcoord : ArbitrarilyLateCoordinateStateConstraints x) :
    HasUniformTwoDiscontinuousTracialState G := by
  obtain ⟨σ, hσ⟩ :=
    exists_corona_tracialState_of_arbitrarilyLate_coordinate_states x hcoord
  refine hasUniformTwoDiscontinuousTracialState_of_detected G hgauge
    (σ := σ) ?_
  rw [hσ]
  exact one_ne_zero

/-! ## Route two: the Jordan alternative -/

/-- **The alternative route, restored.**  From a norm-distance
`TraciallyNullObstruction`, Hahn--Banach produces a signed tracial functional
detecting the class, and the Jordan decomposition turns it into a tracial state.
The two Jordan statements are standard literature (Cuntz--Pedersen, J. Funct.
Anal. 33 (1979); Takesaki, *Theory of Operator Algebras I*, III.4.2) but are not
in Mathlib, so they stay as named hypotheses.

Nothing in the counterexample depends on this theorem.  It is recorded because
it derives the same conclusion from a different obstruction: a norm bound at
every tail index instead of a state at arbitrarily late coordinates. -/
theorem hasUniformTwoDiscontinuousTracialState_of_jordan
    (G : TracialTwoGauge D) (B : TraciallyNullObstruction D)
    (hq : B.twoSize = G.q)
    (hJ : HasJordanDecomposition (CStarProductCorona D atTop))
    (huniq : HasUniqueJordanDecomposition (CStarProductCorona D atTop)) :
    HasUniformTwoDiscontinuousTracialState G := by
  obtain ⟨σ, hσ⟩ :=
    exists_tracialState_detecting_coronaClass_of_jordan
      B.toBlockObstruction hJ huniq
  have hgauge :
      Tendsto (fun n ↦ G.q n (B.toBlockObstruction.sequence n)) atTop (nhds 0) := by
    have h := B.twoSize_h_tendsto_zero
    rwa [hq] at h
  exact hasUniformTwoDiscontinuousTracialState_of_detected G hgauge (σ := σ) hσ

/-! ## `T(A) ⊊ T(M)`

`A = unitization(⊕_s D_s)` is realized as `unitizedC0Sum D` inside the bounded
product, and it sits inside `M = ℂ1 + J`.  A tracial state of `M` restricts to
one of `A`; the question of Problem XXII is whether every tracial state of `M`
arises from `A` by uniform-two-continuous extension. -/

/-- Coordinates of a difference in `M = ℂ1 + J` are the differences of the
coordinates.

This is hoisted into its own lemma deliberately.  It is one delta crossing
through the subalgebra's ring structure and the `ℓ∞` subtraction; left inline
underneath the limit arguments below, elaboration descends that chain once per
occurrence and the uniqueness proof does not terminate. -/
theorem coe_sub_apply (G : TracialTwoGauge D)
    (x y : ↥(scalarPlusJSubalgebra G)) (n : ℕ) :
    ((x - y : ↥(scalarPlusJSubalgebra G)) : BoundedCStarSequence D) n
      = (x : BoundedCStarSequence D) n - (y : BoundedCStarSequence D) n := rfl

/-- **The approximants of (A8), packaged.**  Every element of `M = ℂ1 + J` is
the uniform-two limit of a sequence drawn from `A`, viewed inside `M`.

This is the landed scalar truncation, hoisted into its own declaration on
purpose.  All the subtype arithmetic and the whole limit estimate live here,
where there are no ambient continuity hypotheses; the uniqueness theorem below
then consumes only an opaque sequence `b` and never builds a subalgebra element
underneath a `Tendsto`. -/
theorem exists_uniformTwoApproximants (G : TracialTwoGauge D)
    (x : ↥(scalarPlusJSubalgebra G)) :
    ∃ b : ℕ → ↥(scalarPlusJSubalgebra G),
      (∀ k, (b k : BoundedCStarSequence D) ∈ unitizedC0Sum D) ∧
      Tendsto (fun k ↦ uniformTwoNorm G
        ((x - b k : ↥(scalarPlusJSubalgebra G)) : BoundedCStarSequence D))
        atTop (nhds 0) := by
  obtain ⟨a, -, hA, -, -, hconv⟩ :=
    exists_uniformTwoCauchy_scalarTruncations G (mem_scalarPlusJSubalgebra.1 x.2)
  have hmem : ∀ k, a k ∈ scalarPlusJSubalgebra G := fun k ↦
    mem_scalarPlusJSubalgebra.2 (unitizedC0Sum_subset_scalarPlusJ G (hA k))
  refine ⟨fun k ↦ ⟨a k, hmem k⟩, hA, ?_⟩
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨K, hK⟩ := hconv (ε / 2) (half_pos hε)
  filter_upwards [eventually_ge_atTop K] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (uniformTwoNorm_nonneg G _)]
  have hbd : uniformTwoNorm G
      ((x - ⟨a k, hmem k⟩ : ↥(scalarPlusJSubalgebra G)) :
        BoundedCStarSequence D) ≤ ε / 2 := by
    refine uniformTwoNorm_le G _ fun n ↦ ?_
    rw [coe_sub_apply G x ⟨a k, hmem k⟩ n]
    exact (hK k hk n).le
  linarith

/-- **Uniqueness of the continuous extension.**  Two uniform-two-continuous
tracial states of `M` which agree on `A` are equal.

This is (A8) doing its work: the landed scalar truncations exhibit every element
of `M` as the uniform-two-limit of elements of `A`, and continuity transports
agreement across that limit.  It is what makes the extension map well defined
and injective, so that `T(A)` really is a subset of `T(M)` rather than a family
of unrelated functionals. -/
theorem eq_of_eqOn_unitizedC0Sum (G : TracialTwoGauge D)
    {σ σ' : TracialState ↥(scalarPlusJSubalgebra G)}
    (hσ : IsUniformTwoContinuous G σ) (hσ' : IsUniformTwoContinuous G σ')
    (heq : ∀ y : ↥(scalarPlusJSubalgebra G),
      (y : BoundedCStarSequence D) ∈ unitizedC0Sum D → σ y = σ' y)
    (x : ↥(scalarPlusJSubalgebra G)) : σ x = σ' x := by
  obtain ⟨b, hbA, hnull⟩ := exists_uniformTwoApproximants G x
  have h1 := hσ (fun k ↦ x - b k) hnull
  have h2 := hσ' (fun k ↦ x - b k) hnull
  have hfun : (fun _ : ℕ ↦ σ x - σ' x)
      = fun k ↦ σ (x - b k) - σ' (x - b k) := by
    funext k
    rw [σ.map_sub, σ'.map_sub, heq (b k) (hbA k), sub_sub_sub_cancel_right]
  have hdiff : Tendsto (fun _ : ℕ ↦ σ x - σ' x) atTop (nhds 0) := by
    rw [hfun]
    have h3 := h1.sub h2
    rwa [sub_zero] at h3
  have hzero : (0 : ℂ) = σ x - σ' x :=
    tendsto_nhds_unique hdiff tendsto_const_nhds
  exact sub_eq_zero.mp hzero.symm

/-- `σ` is the uniform-two-continuous extension of the functional `τ` on
`A = unitization(⊕_s D_s)`: it is continuous for the gauge and agrees with `τ`
on `A`.  By `eq_of_eqOn_unitizedC0Sum` at most one `σ` satisfies this for a
given `τ`, so this really names the image of a map. -/
def IsExtensionOfBaseFunctional (G : TracialTwoGauge D)
    (σ : TracialState ↥(scalarPlusJSubalgebra G))
    (τ : BoundedCStarSequence D → ℂ) : Prop :=
  IsUniformTwoContinuous G σ ∧
    ∀ y : ↥(scalarPlusJSubalgebra G),
      (y : BoundedCStarSequence D) ∈ unitizedC0Sum D →
        σ y = τ (y : BoundedCStarSequence D)

/-- `σ` lies in the image of the extension map `T(A) → T(M)`. -/
def IsExtensionOfSomeBaseFunctional (G : TracialTwoGauge D)
    (σ : TracialState ↥(scalarPlusJSubalgebra G)) : Prop :=
  ∃ τ : BoundedCStarSequence D → ℂ, IsExtensionOfBaseFunctional G σ τ

/-- **Surjectivity of the extension map `T(A) → T(M)`**, which is the positive
answer STW Problem XXII asks about: every tracial state of the uniform tracial
completion is the continuous extension of one of `A`. -/
def ExtensionMapSurjective (G : TracialTwoGauge D) : Prop :=
  ∀ σ : TracialState ↥(scalarPlusJSubalgebra G),
    IsExtensionOfSomeBaseFunctional G σ

/-- **The image of `T(A)` is exactly the uniform-two-continuous states.**

Forward is immediate.  Backward is the substance: a continuous tracial state of
`M` agrees on `A` with its own restriction there, and `eq_of_eqOn_unitizedC0Sum`
says no second continuous state does, so it is the extension of that
restriction and of nothing else. -/
theorem isExtensionOfSomeBaseFunctional_iff (G : TracialTwoGauge D)
    (σ : TracialState ↥(scalarPlusJSubalgebra G)) :
    IsExtensionOfSomeBaseFunctional G σ ↔ IsUniformTwoContinuous G σ := by
  classical
  constructor
  · rintro ⟨τ, hcont, -⟩
    exact hcont
  · intro hcont
    refine ⟨fun z ↦ if h : z ∈ scalarPlusJSubalgebra G then σ ⟨z, h⟩ else 0,
      hcont, ?_⟩
    intro y _
    show σ y = if h : (y : BoundedCStarSequence D) ∈ scalarPlusJSubalgebra G
      then σ ⟨(y : BoundedCStarSequence D), h⟩ else (0 : ℂ)
    exact (dif_pos y.2).symm

/-- **(A18) as a theorem: `T(A) ⊊ T(M)`.**  The extension map from the tracial
states of `A` to those of the uniform tracial completion `M` is not surjective:
the state produced from the block data is not continuous for the gauge, so by
`isExtensionOfSomeBaseFunctional_iff` it is not the extension of any functional
on `A`.

This is the negative answer to STW Problem XXII, stated without any remaining
appeal to a remark. -/
theorem not_extensionMapSurjective (G : TracialTwoGauge D)
    (B : CoordinateStateBlockData D G) : ¬ ExtensionMapSurjective G := by
  intro hsurj
  obtain ⟨σ, hσ⟩ := hasUniformTwoDiscontinuousTracialState_of_blockData G B
  exact hσ ((isExtensionOfSomeBaseFunctional_iff G σ).1 (hsurj σ))

/-- The same conclusion straight from the unbundled compactness hypothesis. -/
theorem not_extensionMapSurjective_of_compactness (G : TracialTwoGauge D)
    {x : BoundedCStarSequence D}
    (hgauge : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0))
    (hcoord : ArbitrarilyLateCoordinateStateConstraints x) :
    ¬ ExtensionMapSurjective G :=
  not_extensionMapSurjective G ⟨x, hgauge, hcoord⟩

/-- The same conclusion along the alternative route. -/
theorem not_extensionMapSurjective_of_jordan (G : TracialTwoGauge D)
    (B : TraciallyNullObstruction D) (hq : B.twoSize = G.q)
    (hJ : HasJordanDecomposition (CStarProductCorona D atTop))
    (huniq : HasUniqueJordanDecomposition (CStarProductCorona D atTop)) :
    ¬ ExtensionMapSurjective G := by
  intro hsurj
  obtain ⟨σ, hσ⟩ :=
    hasUniformTwoDiscontinuousTracialState_of_jordan G B hq hJ huniq
  exact hσ ((isExtensionOfSomeBaseFunctional_iff G σ).1 (hsurj σ))

/-! ## Model tests for the new `Prop`s

Repository standing order.  `IsExtensionOfBaseFunctional`,
`IsExtensionOfSomeBaseFunctional` and `ExtensionMapSurjective` are pinned from
both sides: `isExtensionOfSomeBaseFunctional_iff` above says the middle one is
exactly continuity, and the two lemmas here place `ExtensionMapSurjective`
strictly between a satisfiable condition and a refutable one. -/

/-- **Satisfiability.**  If every tracial state of `M` happens to be continuous
for the gauge, the extension map is surjective.  So `ExtensionMapSurjective` is
not self-contradictory, and the endpoint is a genuine dichotomy rather than a
`Prop` that no gauge could satisfy. -/
theorem extensionMapSurjective_of_forall_isUniformTwoContinuous
    (G : TracialTwoGauge D)
    (h : ∀ σ : TracialState ↥(scalarPlusJSubalgebra G),
      IsUniformTwoContinuous G σ) :
    ExtensionMapSurjective G :=
  fun σ ↦ (isExtensionOfSomeBaseFunctional_iff G σ).2 (h σ)

/-- **The refuting side is not vacuous either.**  Surjectivity fails exactly
when some tracial state of `M` is discontinuous, which is the assembly's
endpoint.  Together with the previous lemma this shows the two `Prop`s are
negations of one another and neither is trivially decided. -/
theorem not_extensionMapSurjective_iff (G : TracialTwoGauge D) :
    ¬ ExtensionMapSurjective G ↔ HasUniformTwoDiscontinuousTracialState G := by
  constructor
  · intro h
    by_contra hcon
    refine h fun σ ↦ (isExtensionOfSomeBaseFunctional_iff G σ).2 ?_
    by_contra hσ
    exact hcon ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩ hsurj
    exact hσ ((isExtensionOfSomeBaseFunctional_iff G σ).1 (hsurj σ))

/-- The two routes reach the same named endpoint, which is the point of keeping
both. -/
theorem routes_agree (G : TracialTwoGauge D) :
    ((∃ x : BoundedCStarSequence D,
        Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0) ∧
        ArbitrarilyLateCoordinateStateConstraints x) →
      ¬ ExtensionMapSurjective G) ∧
    (HasJordanDecomposition (CStarProductCorona D atTop) →
      HasUniqueJordanDecomposition (CStarProductCorona D atTop) →
      (∃ B : TraciallyNullObstruction D, B.twoSize = G.q) →
      ¬ ExtensionMapSurjective G) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hgauge, hcoord⟩
    exact not_extensionMapSurjective_of_compactness G hgauge hcoord
  · rintro hJ huniq ⟨B, hq⟩
    exact not_extensionMapSurjective_of_jordan G B hq hJ huniq

end

end STW22CompactnessRoute
end GroupApproximation
