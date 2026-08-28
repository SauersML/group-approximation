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

`not_rotatingQuotient_of_fixes_basepoint` below is that contradiction,
formalized, and it is sharper than the counterexample: **the conclusion of
Theorem 5.3 as stated is unsatisfiable whenever any nontrivial element of the
rotation closure fixes the basepoint.**  Only the claim that the displayed
configuration satisfies all the hypotheses is left unformalized, and that is the
part needing a bespoke two-point pseudometric space; it is written out above in
full so that it can be checked by hand or formalized later.

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
def rotatingQuotientEmpty (ρ : ℝ) (Rot : X → Subgroup G) (y₀ : X) :
    RotatingQuotient ρ (∅ : Set X) Rot y₀ where
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
  injRadius := ρ
  separation_le_injRadius := le_refl ρ
  ne_one_of_dist_lt := fun g hg _ => hg

theorem nonempty_rotatingQuotient_empty (ρ : ℝ) (Rot : X → Subgroup G)
    (y₀ : X) : Nonempty (RotatingQuotient ρ (∅ : Set X) Rot y₀) :=
  ⟨rotatingQuotientEmpty ρ Rot y₀⟩

/-! ## The defect: a fixed basepoint makes the conclusion unsatisfiable -/

/-- **The conclusion of Theorem 5.3 as stated is unsatisfiable whenever a
nontrivial element of the rotation closure fixes the basepoint.**

`g` lies in the kernel, so `q g = 1`; and `g` fixes `y₀`, so it displaces it by
`0 < ρ ≤ injRadius`, and `ne_one_of_dist_lt` demands `q g ≠ 1`.

This is the heart of the refutation in the module header, and it is sharper
than the counterexample there: it needs no hypothesis on the space, on the
family or on `δ`.  What the counterexample adds is that the hypotheses of
`DGOQuotientStatement` do not exclude this configuration -- with a trivial
action on a space whose distances miss the annulus `[20δ, 40δ]`, the very
rotating condition is vacuous and every point is fixed. -/
theorem not_rotatingQuotient_of_fixes_basepoint {ρ : ℝ} (hρ : 0 < ρ)
    {C : Set X} {Rot : X → Subgroup G} {y₀ : X} {g : G} (hg1 : g ≠ 1)
    (hmem : g ∈ rotationNormalClosure C Rot) (hfix : g • y₀ = y₀) :
    IsEmpty (RotatingQuotient ρ C Rot y₀) := by
  constructor
  intro D
  have hker : D.q g = 1 := by
    rw [← MonoidHom.mem_ker, D.ker_eq]
    exact hmem
  have hdist : dist y₀ (g • y₀) < D.injRadius := by
    rw [hfix, dist_self]
    have hsep := D.separation_le_injRadius
    linarith
  exact D.ne_one_of_dist_lt g hg1 hdist hker

/-- **Contrapositive, as the constraint the hypotheses must deliver.**  If
Theorem 5.3 produces a quotient at all, then every nontrivial element of the
rotation closure moves the basepoint.  That is a conclusion about the *action*,
so it can only come from hypotheses about the action -- and the very rotating
condition, which constrains one annulus about each apex, does not reach a
basepoint `ρ`-far from all of them without a geodesic to interpolate along. -/
theorem smul_ne_of_rotatingQuotient {ρ : ℝ} (hρ : 0 < ρ) {C : Set X}
    {Rot : X → Subgroup G} {y₀ : X} (D : RotatingQuotient ρ C Rot y₀) {g : G}
    (hg1 : g ≠ 1) (hmem : g ∈ rotationNormalClosure C Rot) : g • y₀ ≠ y₀ :=
  fun hfix =>
    (not_rotatingQuotient_of_fixes_basepoint hρ hg1 hmem hfix).false D

end Family

/-! ## The repaired statement -/

/-- **DGO, Theorem 5.3, with the hypothesis the transcription dropped.**

`HullSC.DGOQuotientStatement` with `IsGeodesicSpace X` added.  DGO work in
geodesic spaces throughout; without one the very rotating condition constrains
an annulus that can be empty, and `not_rotatingQuotient_of_fixes_basepoint`
turns that into a refutation.

A geodesic supplies the point `x` at distance `30δ` from the apex on `[y₀, c]`
that `dist_le_dist_smul_of_veryRotating` needs, which is the step the argument
turns on.

Applying this at the cone-off needs the geometric realisation of
`GGT/CayleyGeodesicModel.lean`, because
`Manuscript.NonMF.HullFillAxisDichotomy.not_isGeodesicSpace_cayley` proves the
vertex model is not geodesic. -/
def DGOQuotientStatementGeodesic : Prop :=
  ∀ {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (δ ρ : ℝ) (C : Set X) (Rot : X → Subgroup G) (y₀ : X),
      0 < δ → 200 * δ ≤ ρ → IsHyperbolicSpace δ X → IsGeodesicSpace X →
        IsRotatingFamily G X C Rot → IsSeparated C ρ →
          IsVeryRotating G X δ C Rot → (∀ c ∈ C, ρ ≤ dist y₀ c) →
            Nonempty (RotatingQuotient ρ C Rot y₀)

/-- The uncorrected statement implies the corrected one: the repair only adds a
hypothesis.  Recorded so the direction of the correction is visible.  The
converse is not available, and `not_rotatingQuotient_of_fixes_basepoint` with
the counterexample of the module header is why. -/
theorem dgoQuotientStatementGeodesic_of_dgoQuotientStatement
    (h : DGOQuotientStatement.{u, v}) : DGOQuotientStatementGeodesic.{u, v} := by
  intro G _ X _ _ δ ρ C Rot y₀ hδ hρ hhyp _ hfam hsep hvr hfar
  exact h δ ρ C Rot y₀ hδ hρ hhyp hfam hsep hvr hfar

end HullSC
end GroupApproximation
