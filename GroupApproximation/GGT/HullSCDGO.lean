import GroupApproximation.GGT.HullSCRotatingFamily

/-!
# Dahmani-Guirardel-Osin's Theorem 5.3: the plan, and a defect in the statement

Dahmani-Guirardel-Osin, *Hyperbolically embedded subgroups and rotating families
in groups acting on hyperbolic spaces*, Mem. Amer. Math. Soc. 245 (2017),
no. 1156, §5.

`Manuscript.NonMF.TheoremCDebts.dgoTheorem53` is the debt this module is aimed
at.  Before planning the proof it is worth asking whether the statement has a
model, and the answer is that **`HullSC.DGOQuotientStatement` as it stands is
false**.  The counterexample is elementary and is written out below.  So the
first deliverable of this lane is not a proof but a repair.

## The refutation

Take the two-point space `X = {a, b}` with `dist a b = 1`; it embeds
isometrically in `ℝ`, so it is `0`-hyperbolic and therefore `δ`-hyperbolic for
every `δ > 0`.  Let `G` be any nontrivial group **acting trivially** on `X`,
let `C = {a}`, let `Rot a = ⊤`, let `y₀ = b`, and take

    δ = 1/1000,      ρ = 1.

Every hypothesis of `DGOQuotientStatement` holds:

* `0 < δ` and `200 * δ = 1/5 ≤ 1 = ρ`;
* `IsHyperbolicSpace δ X`, since `X` is `0`-hyperbolic;
* `IsRotatingFamily G X C Rot` -- the action is trivial, so it is isometric,
  `C` is invariant, every rotation fixes `a`, and equivariance is
  `h ∈ Rot a ↔ g⁻¹hg ∈ Rot a` between two copies of `⊤`;
* `IsSeparated C ρ` -- vacuous, `C` is a singleton;
* `IsVeryRotating G X δ C Rot` -- **vacuous**, because the annulus it quantifies
  over is `20δ ≤ dist x a ≤ 40δ`, that is `0.02 ≤ dist x a ≤ 0.04`, and every
  distance in `X` is `0` or `1`;
* `∀ c ∈ C, ρ ≤ dist y₀ c` -- `dist b a = 1 = ρ`.

But the conclusion fails.  `rotationNormalClosure C Rot = ⊤`, so `ker q = ⊤`
and `q g = 1` for every `g`; while for `g ≠ 1` the trivial action gives
`dist y₀ (g · y₀) = 0 < ρ ≤ injRadius`, so `ne_one_of_dist_lt` demands
`q g ≠ 1`.  No `RotatingQuotient` exists.

The contradiction is sharper than the counterexample: **the conclusion was
unsatisfiable whenever any nontrivial element of the rotation closure fixes the
basepoint**, with no hypothesis on the space, the family or `δ`.

**This is now resolved, and by removing the clause rather than by adding a
hypothesis.**  The provenance audit below shows `ne_one_of_dist_lt` was never
DGO's, so it has moved to `HullSCFilling.RotatingData.injOn_of_dist`.
`DGOQuotientStatement` no longer carries a metric clause, and the configuration
above no longer refutes it: with the kernel everything and the quotient trivial,
the dichotomy and the finite-order clause both hold vacuously.  The statement
was false exactly because it claimed something its citation does not prove.

What the counterexample now bears on is the clause in its new home: it shows
that `injOn_of_dist` has to be *proved* by Hull's §5 and cannot be inherited,
since a family can satisfy every rotating hypothesis and still fix the
basepoint.  The two formalized lemmas that recorded the contradiction are gone
with the clause; the configuration is written out above in full so that it can
be checked by hand or formalized against the new home.

## Why the previous two repairs did not catch it

`eq_one_of_dist_lt_everywhere` refuted the displacement clause stated at every
point, because a rotation fixes its apex; the repair moved the clause to a
basepoint `y₀` kept `ρ`-far from every apex.  That repair is correct and
necessary, and it is not enough: under a trivial action *every* point is fixed,
so moving the basepoint away from the apices does not make the rotation move it.
The clause needs the rotation to actually displace `y₀`, and nothing in the
hypotheses delivers that.

## The repair, and the tension it creates

`IsVeryRotating` constrains only the annulus `20δ ≤ dist · c ≤ 40δ`, while
`ne_one_of_dist_lt` is a claim at a point with `dist y₀ c ≥ ρ ≥ 200δ` -- far
outside it.  In DGO the bridge between the two is the geodesic geometry: given
`y₀` at distance at least `ρ` from `c`, one takes the point `x` of a geodesic
`[y₀, c]` at distance `30δ` from `c`, which *is* in the annulus, applies the
very rotating condition there to get `dist x (g · x) ≥ 50δ` -- this repository
already proves that step, `dist_le_dist_smul_of_veryRotating` -- and propagates
it back to `y₀` by hyperbolicity.  **That argument needs a point at distance
`30δ` from `c` to exist**, which is exactly what a geodesic space supplies and
what the two-point space above does not.

So the honest repair is `DGOQuotientStatementGeodesic` below: the same
statement with `IsGeodesicSpace X` added.  DGO work in geodesic spaces
throughout, so this is not a weakening of their theorem but a transcription
error being corrected.

The repair has a cost, and whoever takes this lane should know it before
writing any of §5.  `Manuscript.NonMF.HullFillAxisDichotomy.not_isGeodesicSpace_cayley`
**proves** that `Cayley A` is not a geodesic space for a nontrivial group -- the
vertex model has integer distances and `IsGeodesicSpace` asks for a point at
every real parameter.  The cone-off that Hull's Theorem 5.1 applies Theorem 5.3
to is a `Cayley`, so the repaired statement cannot be applied there directly.
The route is the geometric realisation being built in
`GGT/CayleyGeodesicModel.lean` and `GGT/CayleyGeodesicRealisation.lean` --
`Point A` is base, letter and a parameter in `[0,1]` -- with the family
transported to the realisation and the conclusion transported back along the
vertex inclusion.  That transfer is a lane of its own and it is a prerequisite,
not a detail.

## A second finding: `IsVeryRotating` is not DGO's condition

Read against the paper (arXiv:1111.7048), **Definition 2.12(c)** -- the very
rotating condition -- says: for `c ∈ C`, `g ∈ G_c \ {1}` and `x, y` with
`d(x,c), d(y,c) ∈ [20δ, 40δ]` **and `d(g·x, y) ≤ 15δ`**, *any geodesic between
`x` and `y` contains `c`*.

`HullSC.IsVeryRotating` differs in both halves.  It drops the coupling
hypothesis `d(g·x, y) ≤ 15δ`, quantifying over every pair in the annulus; and
it replaces "every geodesic from `x` to `y` passes through `c`" by the Gromov
product bound `(x | g·y)_c ≤ 5δ`.  Dropping a hypothesis from a *hypothesis* of
the theorem makes the condition harder to satisfy, so `DGOQuotientStatement`
was, in this respect, weaker than DGO's theorem and still false -- the
counterexample above satisfies the strengthened condition vacuously either way.
But it matters for anyone *building* a family: a family satisfying DGO's
Definition 2.12(c) need not satisfy `IsVeryRotating`, so the construction has to
be checked against the definition in this repository and not against the paper.

Restating `IsVeryRotating` as Definition 2.12(c) verbatim is the natural repair
and it is not done here, because the geodesic form is unstateable until the
space is known to be geodesic -- which is the same prerequisite as above, and
which is why the two repairs should land together rather than separately.

## A third finding: which clauses are actually DGO's, and which are used

Read Theorem 5.3 against the source and `hullQuotient_of_fillingData` against
this repository, and the attribution comes out inverted.  **Theorem 5.3 has
exactly two conclusions:**

> (a) There exists a (usually infinite) subset `T ⊆ G` such that
>     `⟨⟨H⟩⟩^G = ∗_{t ∈ T} t⁻¹ H t`.
> (b) Every element `h ∈ ⟨⟨H⟩⟩^G` either is conjugate to an element of `H`, or
>     is loxodromic with respect to the action on `𝕏`.

Against the six clauses of `RotatingQuotient`:

* `ker_eq` and `surjective` -- by construction, not cited.
* `rotation_or_loxodromic` -- **this is 5.3(b), correctly attributed, and it is
  never used.**  `hullQuotient_of_fillingData` consumes `Q`, `group`, `q`,
  `surjective`, `ker_eq`, `injRadius`, `separation_le_injRadius`,
  `ne_one_of_dist_lt` and `finiteOrder_lift`.  It does not touch the dichotomy.
* `finiteOrder_lift` -- **not a conclusion of Theorem 5.3**, and it is used.
  It is a corollary of 5.3(a): the normal closure is a free product of
  conjugates of `H`, so it acts on the Bass-Serre tree of that splitting with
  the conjugates as vertex stabilizers, and a finite subgroup of a group acting
  on a tree fixes a point, hence is conjugate into a factor.  That is the
  standard route and it goes through the splitting, not through the dichotomy.
* `injRadius`, `separation_le_injRadius`, `ne_one_of_dist_lt` -- **not a
  conclusion of Theorem 5.3, and not derivable from either of its two.**  The
  dichotomy gives loxodromy, which is an asymptotic lower bound on
  `d(y, gⁿ·y)` with an additive constant, and no bound at `n = 1`; the splitting
  says nothing metric.  The nearest statement in the paper is Theorem 2.17(b),
  *the quotient map `𝕏 → 𝕏/⟨⟨H⟩⟩^G` is a local isometry away from the apices* --
  which is about the quotient of the **space**, not about the kernel of the
  quotient of the **group**, and those are different statements.

So the structure is carrying one clause of DGO's that nothing consumes, is
missing the clause of DGO's that another of its clauses depends on, and is
attributing to DGO a metric clause that appears to be Hull's own §5 work.

**The repair has been made, and one line of the audit above needed correcting
in the making of it.**

* `injRadius`, `separation_le_injRadius` and `ne_one_of_dist_lt` are out of
  `RotatingQuotient` and into `HullSCFilling.RotatingData.injOn_of_dist`, where
  the cone-off and its basepoint are in scope.  With them went the basepoint
  parameter and the separation parameter of the structure, neither of which any
  remaining clause mentions -- DGO's conclusion has no basepoint.
* `rotation_or_loxodromic` is **not** dead weight, and the audit was wrong to
  imply it.  `HullSCRotatingFamily.conj_into_rot_of_isOfFinOrder` derives from
  it that a finite-order element of the kernel is conjugate into a rotation
  subgroup -- a loxodromic element has infinite order -- and that is the first
  step of the finite-order lifting clause.  It was unconsumed only because
  nothing had yet been proved from it.
* 5.3(a), the free splitting, is **not** added.  The audit said
  `finiteOrder_lift` rests on it; the conjugacy step turns out to come from the
  dichotomy instead, so what the splitting is needed for is the narrower
  order-preserving half of the lift.  Stating it faithfully means a `CoprodI`
  over a set of orbit representatives and a new import into
  `GGT/HullSCRotatingFamily.lean`, for a clause with no consumer until that half
  is attempted.

  **The order-preserving half of `finiteOrder_lift` is therefore still owed, and
  it rests on the splitting.**  `conj_into_rot_of_isOfFinOrder` gets a
  finite-order element of the kernel conjugated into a rotation subgroup; it does
  not produce a preimage *of the same order*, which is what the field asserts.
  Until that is proved the field is a citation with no source in Theorem 5.3 --
  do not read it as fully attributed.  Whoever attempts it should start from
  this statement rather than re-derive it:

      freeSplitting : ∃ (T : Type u) (apex : T → X) (conj : T → G)
        (φ : Monoid.CoprodI (fun i : T => ↥(Rot (apex i))) →* G),
          (∀ i, apex i ∈ C) ∧ Function.Injective φ ∧
            φ.range = rotationNormalClosure C Rot ∧
            ∀ (i : T) (x : ↥(Rot (apex i))),
              φ (Monoid.CoprodI.of x) = conj i * (x : G) * (conj i)⁻¹

  and the route to the field is the Bass-Serre tree of that splitting: a finite
  subgroup acting on a tree fixes a point, so it is conjugate into a vertex
  stabiliser, which is a conjugate of some `Rot c`.

## The plan for §5, in dependency order

Once the statement is repaired, DGO's proof is the following chain.  Nothing
below is formalized here; this is the map, and the numbering is the paper's.

**(1) The definitions.**  DGO Definition 2.12(a) is the rotating family, 2.12(b)
is `ρ`-separation, 2.12(c) is the very rotating condition.  Those and the
elementary displacement estimates are in `GGT/HullSCRotatingFamily.lean`:
`dist_smul_apex_eq`, `dist_le_dist_smul_of_veryRotating`, `ne_of_veryRotating`,
`eq_of_dist_lt_of_isSeparated`.

**(2) Windmills** (DGO §5.1).  The inductive object of the proof: a subspace
built by attaching, at each stage, the apices within a controlled distance of
what is already there together with their rotation orbits.  A windmill is
quasi-convex with a constant independent of the stage, and the group generated
by the rotations at its apices acts on it.  This is the induction that replaces
the van Kampen diagram of classical small cancellation, and it is where the
hyperbolicity constant is spent.

**(3) The Greendlinger-type lemmas** (DGO §5.1.3).  A nontrivial element of
`K = ⟨⟨Rot c⟩⟩` that is not conjugate into a single `Rot c` moves every point of
a windmill a definite amount.  This is what gives, at one stroke, the dichotomy
`rotation_or_loxodromic`, the injectivity radius `ne_one_of_dist_lt`, and --
through a windmill containing a lift of a finite-order element -- the lifting
clause `finiteOrder_lift`.

**(4) The theorem.**  DGO **Theorem 5.3**, restated for `α`-rotating subgroups
with `α ≥ 200` as their **Theorem 2.14**, which is where the `200 * δ ≤ ρ` of
`DGOQuotientStatement` comes from.  Its two printed conclusions are
`⟨⟨H⟩⟩^G = ∗_{t ∈ T} t⁻¹ H t` -- the free splitting -- and *every element of
`⟨⟨H⟩⟩^G` is either conjugate into `H` or loxodromic*, which is
`rotation_or_loxodromic`.  **`finiteOrder_lift` and the injectivity radius are
not among those two clauses**, so before they are proved someone has to find
where in §5 they come from; they may be corollaries of the free splitting rather
than of the dichotomy.  That is the first thing to check and it is not yet
checked.

**(5) The free splitting.**  Not recorded in `RotatingQuotient`, because nothing
above it consumes the splitting -- but see (4): if the lifting clause is a
corollary of the splitting rather than of the Greendlinger lemma, it has to be
added after all.

A realistic ordering is (1) then (3), with the windmill induction of (2) stated
as a named `Prop` and consumed rather than proved first: the windmill
construction is the longest part of §5 and the Greendlinger lemmas are what the
clauses need.

The numbering above is read off the ar5iv rendering of arXiv:1111.7048 rather
than the published Memoir, and the two differ: what the rendering shows as
Theorem 2.14 it also identifies as Theorem 5.3 in the body.  Where a docstring
below cites a number, it cites that source.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u v

section Family

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## The conclusion is consistent: the empty family is a model -/

/-- With no apices there are no rotations, so the subgroup they generate is
trivial. -/
theorem rotationNormalClosure_empty (Rot : X → Subgroup G) :
    rotationNormalClosure (∅ : Set X) Rot = ⊥ := by
  have hset : {g : G | ∃ c ∈ (∅ : Set X), g ∈ Rot c} = (∅ : Set G) := by
    ext g
    simp
  show Subgroup.normalClosure {g : G | ∃ c ∈ (∅ : Set X), g ∈ Rot c} = ⊥
  rw [hset]
  exact le_antisymm (Subgroup.normalClosure_le_normal (Set.empty_subset _)) bot_le

/-- **`RotatingQuotient` is inhabitable**: the empty family, with the identity
as quotient map, satisfies every clause.

This is the check that the ten clauses of the conclusion are not mutually
contradictory -- the question that should be asked of every predicate before it
is consumed, and the one whose absence let three statements of this lane be
landed refuted.  It says nothing about `DGOQuotientStatement`, which quantifies
over all families and is false; it says that the *shape* of the conclusion is
sound and that the defect is in the hypotheses. -/
def rotatingQuotientEmpty (Rot : X → Subgroup G) :
    RotatingQuotient (∅ : Set X) Rot where
  Q := G
  group := inferInstance
  q := MonoidHom.id G
  surjective := fun y => ⟨y, rfl⟩
  ker_eq := by
    rw [rotationNormalClosure_empty]
    ext x
    simp [MonoidHom.mem_ker]
  rotation_or_loxodromic := by
    intro g hg hg1
    rw [rotationNormalClosure_empty, Subgroup.mem_bot] at hg
    exact absurd hg hg1
  finiteOrder_lift := fun y _ => ⟨y, rfl, rfl⟩

theorem nonempty_rotatingQuotient_empty (Rot : X → Subgroup G) :
    Nonempty (RotatingQuotient (∅ : Set X) Rot) :=
  ⟨rotatingQuotientEmpty Rot⟩

end Family

/-! ## Why the geodesic hypothesis is the repair -/

/-- **A geodesic realises every intermediate distance.**  On a geodesic from `c`
to `y`, the point at parameter `r` is at distance exactly `r` from `c`. -/
theorem exists_dist_eq_of_geodesic {X : Type v} [PseudoMetricSpace X]
    (hgeo : IsGeodesicSpace X) (c y : X) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ dist c y) : ∃ x : X, dist x c = r := by
  obtain ⟨f, hf, hf0, -⟩ := hgeo c y
  refine ⟨f r, ?_⟩
  have h := hf r ⟨hr0, hr⟩ 0 ⟨le_refl 0, dist_nonneg⟩
  rw [hf0, sub_zero, abs_of_nonneg hr0] at h
  exact h

/-- **In the repaired statement the annulus is never empty.**

The counterexample of the module header works by making the annulus
`20δ ≤ dist · c ≤ 40δ` contain no point at all, so that `IsVeryRotating` holds
vacuously and constrains nothing.  A geodesic closes exactly that hole: a point
at distance at least `ρ ≥ 200δ` from the apex is joined to it by a geodesic
realising every distance up to that, and `30δ` is one of them.

This is what makes `dist_le_dist_smul_of_veryRotating` applicable, which is the
step DGO's argument turns on, and it is why `DGOQuotientStatementGeodesic` keeps
the geodesic hypothesis even though the counterexample no longer refutes the
statement: the hypothesis is now needed for provability rather than for truth.
Hull's §5 needs it too, to prove `RotatingData.injOn_of_dist` in its new home. -/
theorem exists_mem_annulus {X : Type v} [PseudoMetricSpace X]
    (hgeo : IsGeodesicSpace X) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 200 * δ ≤ ρ)
    {c y₀ : X} (hfar : ρ ≤ dist y₀ c) :
    ∃ x : X, 20 * δ ≤ dist x c ∧ dist x c ≤ 40 * δ := by
  have hcy : ρ ≤ dist c y₀ := by rwa [dist_comm] at hfar
  obtain ⟨x, hx⟩ := exists_dist_eq_of_geodesic hgeo c y₀ (r := 30 * δ)
    (by linarith) (by linarith)
  exact ⟨x, by rw [hx]; linarith, by rw [hx]; linarith⟩

/-! ## The repaired statement -/

/-- **DGO, Theorem 5.3, with the hypothesis the transcription dropped.**

`HullSC.DGOQuotientStatement` with `IsGeodesicSpace X` added.  DGO work in
geodesic spaces throughout; without one the very rotating condition constrains
an annulus that can be empty, which is how the counterexample of the module
header got through before the misattributed metric clause was moved out.

A geodesic supplies the point `x` at distance `30δ` from the apex on `[y₀, c]`
that `dist_le_dist_smul_of_veryRotating` needs, which is the step the argument
turns on.

Applying this at the cone-off needs the geometric realisation of
`GGT/CayleyGeodesicModel.lean`, because
`Manuscript.NonMF.HullFillAxisDichotomy.not_isGeodesicSpace_cayley` proves the
vertex model is not geodesic. -/
def DGOQuotientStatementGeodesic : Prop :=
  ∀ {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (δ ρ : ℝ) (C : Set X) (Rot : X → Subgroup G),
      0 < δ → 200 * δ ≤ ρ → IsHyperbolicSpace δ X → IsGeodesicSpace X →
        IsRotatingFamily G X C Rot → IsSeparated C ρ →
          IsVeryRotating G X δ C Rot → Nonempty (RotatingQuotient C Rot)

/-- The uncorrected statement implies the corrected one: the repair only adds a
hypothesis.  Recorded so the direction of the correction is visible.  The
converse is not available: DGO's proof of §5 uses geodesics throughout, and the
counterexample of the module header shows what a non-geodesic space lets
through. -/
theorem dgoQuotientStatementGeodesic_of_dgoQuotientStatement
    (h : DGOQuotientStatement.{u, v}) : DGOQuotientStatementGeodesic.{u, v} := by
  intro G _ X _ _ δ ρ C Rot hδ hρ hhyp _ hfam hsep hvr
  exact h δ ρ C Rot hδ hρ hhyp hfam hsep hvr

end HullSC
end GroupApproximation
