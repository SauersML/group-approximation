import GroupApproximation.GGT.HullSCConeOff
import GroupApproximation.Manuscript.NonMF.Saturation

/-!
# Rotating families, very rotating families, and the quotient theorem of DGO

Dahmani-Guirardel-Osin, *Hyperbolically embedded subgroups and rotating
families in groups acting on hyperbolic spaces*, Mem. Amer. Math. Soc. 245
(2017), no. 1156, §5.  This module writes down the two definitions (§5.1,
§5.3) and the statement of their Theorem 5.3, and proves the elementary
displacement facts that the definition of a very rotating family forces.

## The definitions

A **rotating family** for an isometric action of `G` on `X` is a `G`-invariant
set `C ⊆ X` of *apices* together with, for each apex `c`, a *rotation subgroup*
`Rot c ≤ G` fixing `c`, the assignment being equivariant:
`Rot (g · c) = g (Rot c) g⁻¹`.  It is **ρ-separated** when distinct apices are
at distance at least `ρ`.

It is **very rotating** in the sense of DGO Definition 2.12(c), transcribed
verbatim: for a nontrivial rotation `g` about `c` and points `x`, `y` of the
annulus `20δ ≤ d(·, c) ≤ 40δ` with `d(g·x, y) ≤ 15δ`, *any geodesic between `x`
and `y` contains `c`*.  An earlier form dropped the coupling hypothesis and
stated a Gromov product bound in place of the geodesic conclusion; neither half
was the paper's, and a family built to satisfy the paper would not have met it.

## What is proved, and what is stated

Proved: the elementary consequences of the definitions.

* `dist_smul_apex_eq` -- a rotation about `c` preserves distance to `c`.
* `dist_smul_eq_two_mul_of_veryRotating` -- **a nontrivial rotation displaces a
  point of the annulus by exactly twice its distance to the apex**:
  `d(x, g·x) = 2 d(x,c)`.  Apply the condition at `y = g·x`: the coupling
  `d(g·x, g·x) = 0 ≤ 15δ` is free, and `g·x` is in the annulus because a
  rotation preserves the distance to its apex, so a geodesic from `x` to `g·x`
  passes through `c` and the two halves are equal.  This is the whole force of
  the condition, and the equality is sharper than the `2 d(x,c) - 10δ` the
  Gromov-product form gave.  `dist_le_dist_smul_of_veryRotating` is the
  inequality form, kept for the citations that name it.
* `ne_of_veryRotating` -- consequently a nontrivial rotation fixes no point of
  the annulus, when `δ > 0`.  All three carry `IsGeodesicSpace`: the conclusion
  of 2.12(c) is about geodesics and says nothing where none exist.
* `eq_of_dist_lt_of_isSeparated` -- two apices closer than `ρ` coincide.
* `eq_one_of_dist_lt_everywhere`, `not_rotation_or_loxodromic_of_empty` -- **two
  refutations**, which is why `RotatingQuotient` has the shape it has.  The
  displacement clause may not be stated at every point of `X`: a nontrivial
  rotation fixes its apex and lies in the kernel, so the unrestricted clause
  forces every rotation subgroup to be trivial.  And the dichotomy for the
  elements of `K` may not include `1`: with no apices, `K` is trivial and its
  one element is neither conjugate into a rotation subgroup nor loxodromic.  So
  the displacement clause travels with the family data, which has a basepoint,
  and the structure states the dichotomy for `g ≠ 1`.

Stated and cited, not proved: `DGOQuotientStatement`, DGO's Theorem 5.3.  What
it records is the kernel and the dichotomy for its elements, and that is now all
of it.  Its clause that `K = ⟨⟨Rot c : c ∈ C⟩⟩` is the *free product* of a
family of conjugates of the rotation subgroups is not recorded, because nothing
above it consumes the free splitting, and carrying an unconsumed clause would
put weight on a statement no proof checks.

Two clauses that were recorded here are gone, both of them misattributions.  The
injectivity radius is Hull's §5, and is now
`HullSCFilling.RotatingData.kernel_moves_base`; Hull's Theorem 5.1 turns it into
injectivity on a ball of `Γ(G,A)` through
`HullSCFilling.injOn_cayleyBall_of_kernel_moves`, which is proved.  The lifting
of finite order is Hull's §5 as well (issue #50): the statement carrying it is
false, `GGT/DGORotatingQuotientRefutation.lean` refutes it at a one-point space
where the very rotating condition is vacuous, and neither the dichotomy nor the
free splitting implies it -- `GGT/DGOFreeSplittingOnePoint.lean` proves the same
model satisfies 5.3(a).  It is now
`HullSCFilling.RotatingData.finiteOrder_lift`.

`torsionFree_of_dgoQuotient` is the consumer: over a torsion-free `G`, and
*given the lifting clause*, the quotient by a very rotating family is
torsion-free, which is the clause of Hull's Theorem 5.1 that the torsion-free
lane of this repository needs.  The lifting clause is a hypothesis there for the
reason above, and the family Hull builds is what discharges it.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section Family

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## Rotating families -/

/-- **A rotating family** (DGO): a `G`-invariant set of apices `C`, and for
each apex `c` a subgroup `Rot c` of the stabilizer of `c`, chosen
equivariantly. -/
structure IsRotatingFamily (G : Type u) (X : Type v) [Group G]
    [PseudoMetricSpace X] [MulAction G X] (C : Set X) (Rot : X → Subgroup G) :
    Prop where
  /-- `G` acts by isometries. -/
  isometric : IsIsometricAction G X
  /-- The set of apices is `G`-invariant. -/
  apex_smul : ∀ (g : G) {c : X}, c ∈ C → g • c ∈ C
  /-- Rotations about `c` fix `c`. -/
  rot_fix : ∀ {c : X}, c ∈ C → ∀ g ∈ Rot c, g • c = c
  /-- Equivariance: `Rot (g · c) = g (Rot c) g⁻¹`. -/
  rot_equivariant : ∀ (g : G) {c : X}, c ∈ C → ∀ h : G,
    h ∈ Rot (g • c) ↔ g⁻¹ * h * g ∈ Rot c

/-- **`ρ`-separation** (DGO): distinct apices are far apart. -/
def IsSeparated (C : Set X) (ρ : ℝ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → ρ ≤ dist c c'

/-- **A very rotating family**, Dahmani-Guirardel-Osin Definition 2.12(c),
verbatim: for `c ∈ C`, `g ∈ Rot c \ {1}` and `x, y` with `d(x,c)` and `d(y,c)`
in `[20δ, 40δ]` **and `d(g·x, y) ≤ 15δ`**, any geodesic between `x` and `y`
contains `c`.

An earlier form of this definition dropped the coupling hypothesis
`d(g·x, y) ≤ 15δ` and replaced the geodesic conclusion by the Gromov product
bound `(x | g·y)_c ≤ 5δ`.  Neither half was DGO's, and a family built to satisfy
the paper need not have satisfied it: dropping a hypothesis from a hypothesis
makes the condition harder to meet.  The reading recorded here is the paper's.

"Any geodesic between `x` and `y` contains `c`" is a statement about every
parametrisation realising the distance, which is why it is quantified over `f`
rather than asserted of one chosen geodesic; and it is only usable in a space
where such an `f` exists, which is why every consumer below carries
`IsGeodesicSpace`. -/
def IsVeryRotating (G : Type u) (X : Type v) [Group G] [PseudoMetricSpace X]
    [MulAction G X] (δ : ℝ) (C : Set X) (Rot : X → Subgroup G) : Prop :=
  ∀ c ∈ C, ∀ g ∈ Rot c, g ≠ 1 → ∀ x y : X,
    20 * δ ≤ dist x c → dist x c ≤ 40 * δ →
      20 * δ ≤ dist y c → dist y c ≤ 40 * δ →
        dist (g • x) y ≤ 15 * δ →
          ∀ f : ℝ → X, IsGeodesicSegment f 0 (dist x y) → f 0 = x →
            f (dist x y) = y → ∃ s ∈ Set.Icc (0 : ℝ) (dist x y), f s = c

/-- **The subgroup generated by the rotations**: the normal closure of every
rotation about every apex.  DGO's Theorem 5.3 is about the quotient by it. -/
def rotationNormalClosure (C : Set X) (Rot : X → Subgroup G) : Subgroup G :=
  Subgroup.normalClosure {g : G | ∃ c ∈ C, g ∈ Rot c}

omit [PseudoMetricSpace X] [MulAction G X] in
/-- A rotation about an apex lies in the subgroup the rotations generate. -/
theorem mem_rotationNormalClosure {C : Set X} {Rot : X → Subgroup G} {c : X}
    (hc : c ∈ C) {g : G} (hg : g ∈ Rot c) :
    g ∈ rotationNormalClosure C Rot :=
  Subgroup.subset_normalClosure ⟨c, hc, hg⟩

/-! ## What the definitions force -/

/-- A rotation about `c` preserves the distance to `c`: it fixes `c` and acts
by isometries. -/
theorem dist_smul_apex_eq {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) {c : X} (hc : c ∈ C) {g : G}
    (hg : g ∈ Rot c) (x : X) : dist (g • x) c = dist x c := by
  have hfix : g • c = c := hfam.rot_fix hc g hg
  calc dist (g • x) c = dist (g • x) (g • c) := by rw [hfix]
    _ = dist x c := hfam.isometric g x c

/-- **The displacement estimate of a very rotating family.**  A nontrivial
rotation about `c` moves a point of the annulus about `c` by at least twice its
distance to the apex, up to `10δ`.

This is the inequality the very rotating condition exists to provide: a point
and its rotate lie on opposite sides of the apex, so the distance between them
is the sum of the two radii up to bounded error. -/
theorem dist_smul_eq_two_mul_of_veryRotating {δ : ℝ} {C : Set X}
    {Rot : X → Subgroup G} (hgeo : IsGeodesicSpace X)
    (hfam : IsRotatingFamily G X C Rot) (hvr : IsVeryRotating G X δ C Rot)
    {c : X} (hc : c ∈ C) {g : G} (hg : g ∈ Rot c) (hg1 : g ≠ 1) {x : X}
    (hlow : 20 * δ ≤ dist x c) (hhigh : dist x c ≤ 40 * δ) :
    dist x (g • x) = 2 * dist x c := by
  have hδ0 : (0 : ℝ) ≤ δ := by
    have hnn : (0 : ℝ) ≤ dist x c := dist_nonneg
    linarith
  have hrad : dist (g • x) c = dist x c := dist_smul_apex_eq hfam hc hg x
  obtain ⟨f, hf, hf0, hf1⟩ := hgeo x (g • x)
  obtain ⟨s, hs, hfs⟩ := hvr c hc g hg hg1 x (g • x) hlow hhigh
    (by rw [hrad]; exact hlow) (by rw [hrad]; exact hhigh)
    (by rw [dist_self]; linarith) f hf hf0 hf1
  have hA : dist x c = s := by
    have h := hf 0 ⟨le_refl 0, dist_nonneg⟩ s hs
    rw [hf0, hfs, zero_sub, abs_neg, abs_of_nonneg hs.1] at h
    exact h
  have hB : dist c (g • x) = dist x (g • x) - s := by
    have h := hf s hs (dist x (g • x)) ⟨dist_nonneg, le_refl _⟩
    rw [hfs, hf1, abs_of_nonpos (by linarith [hs.2])] at h
    linarith
  have hC : dist c (g • x) = dist x c := by
    rw [dist_comm]
    exact hrad
  linarith

/-- **The displacement estimate, in the inequality form the plan cites.**  A
weakening of the equality above, kept because `10δ` of slack is what the
argument downstream actually needs and what DGO's own estimate leaves. -/
theorem dist_le_dist_smul_of_veryRotating {δ : ℝ} {C : Set X}
    {Rot : X → Subgroup G} (hgeo : IsGeodesicSpace X)
    (hfam : IsRotatingFamily G X C Rot) (hvr : IsVeryRotating G X δ C Rot)
    {c : X} (hc : c ∈ C) {g : G} (hg : g ∈ Rot c) (hg1 : g ≠ 1) {x : X}
    (hlow : 20 * δ ≤ dist x c) (hhigh : dist x c ≤ 40 * δ) :
    2 * dist x c - 10 * δ ≤ dist x (g • x) := by
  have heq := dist_smul_eq_two_mul_of_veryRotating hgeo hfam hvr hc hg hg1
    hlow hhigh
  have hδ0 : (0 : ℝ) ≤ δ := by
    have hnn : (0 : ℝ) ≤ dist x c := dist_nonneg
    linarith
  linarith

/-- A nontrivial rotation fixes no point of the annulus about its apex. -/
theorem ne_of_veryRotating {δ : ℝ} (hδ : 0 < δ) (hgeo : IsGeodesicSpace X)
    {C : Set X} {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) {c : X} (hc : c ∈ C) {g : G}
    (hg : g ∈ Rot c) (hg1 : g ≠ 1) {x : X} (hlow : 20 * δ ≤ dist x c)
    (hhigh : dist x c ≤ 40 * δ) : g • x ≠ x := by
  intro hfix
  have hdisp := dist_smul_eq_two_mul_of_veryRotating hgeo hfam hvr hc hg hg1
    hlow hhigh
  rw [hfix, dist_self] at hdisp
  linarith

/-- Distinct apices of a `ρ`-separated family are `ρ` apart, so apices closer
than `ρ` coincide. -/
theorem eq_of_dist_lt_of_isSeparated {C : Set X} {ρ : ℝ}
    (hsep : IsSeparated C ρ) {c c' : X} (hc : c ∈ C) (hc' : c' ∈ C)
    (hlt : dist c c' < ρ) : c = c' := by
  by_contra hne
  exact absurd (hsep c hc c' hc' hne) (not_le.mpr hlt)

/-! ## Two clauses that cannot be recorded naively -/

/-- **The displacement clause cannot be stated at every point of `X`.**

A nontrivial rotation fixes its apex and lies in the subgroup the rotations
generate, which is the kernel.  So at `y = c` the displacement is `0`, below any
positive injectivity radius, and a clause reading *"nothing that moves some
point by less than the injectivity radius is killed"* would say the rotation
survives while the kernel clause says it dies.  The two together force every
rotation subgroup to be trivial, which is what this theorem proves.

DGO's estimate is for points **far from the apices**; it is false at the apices.
That is why `RotatingQuotient` below carries a basepoint and
`DGOQuotientStatement` asks for it to be `ρ`-far from every apex. -/
theorem eq_one_of_dist_lt_everywhere {Y : Type*} [Group Y] {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot) {q : G →* Y}
    {L : ℝ} (hL : 0 < L) (hker : q.ker = rotationNormalClosure C Rot)
    (hne : ∀ g : G, g ≠ 1 → ∀ y : X, dist y (g • y) < L → q g ≠ 1) {c : X}
    (hc : c ∈ C) {g : G} (hg : g ∈ Rot c) : g = 1 := by
  by_contra hg1
  have hfix : g • c = c := hfam.rot_fix hc g hg
  have hdist : dist c (g • c) < L := by
    rw [hfix, dist_self]
    exact hL
  have hq1 : q g ≠ 1 := hne g hg1 c hdist
  have hmem : g ∈ q.ker := by
    rw [hker]
    exact mem_rotationNormalClosure hc hg
  exact hq1 (MonoidHom.mem_ker.mp hmem)

/-- **The dichotomy has to exclude the identity.**

With no apices the rotations generate the trivial subgroup, whose one element is
`1`: it is conjugate into no `Rot c`, there being no `c`, and it is not
loxodromic, a loxodromic element having infinite order.  So the clause *"every
element of `K` is conjugate into some `Rot c` or is loxodromic"* is false as
soon as `X` has a point, and `RotatingQuotient` records it for the elements of
`K` other than `1`, which is DGO's own statement. -/
theorem not_rotation_or_loxodromic_of_empty {Rot : X → Subgroup G} (x : X)
    (h : ∀ g ∈ rotationNormalClosure (∅ : Set X) Rot,
      (∃ (a : G) (c : X), c ∈ (∅ : Set X) ∧ a⁻¹ * g * a ∈ Rot c) ∨
        ∀ y : X, IsLoxodromic g y) : False := by
  have h1 : (1 : G) ∈ rotationNormalClosure (∅ : Set X) Rot := one_mem _
  rcases h 1 h1 with ⟨-, c, hc, -⟩ | hlox
  · simp at hc
  · exact not_isOfFinOrder_of_isLoxodromic (hlox x) IsOfFinOrder.one

/-! ## The quotient of DGO's Theorem 5.3 -/

/-- **The quotient produced by DGO's Theorem 5.3.**  Its fields are the clause
of that theorem which the small cancellation theory above it consumes, and the
bookkeeping that carries it:

> Every element of `K = ⟨⟨Rot c : c ∈ C⟩⟩` other than `1` is either conjugate
> into some `Rot c`, or acts loxodromically on `X`.

**Two clauses have left this structure, and both left for the same reason.**

The injectivity radius went first.  It was a field, with a basepoint parameter
to carry it, until the clauses were read against the source: DGO's Theorem 5.3
concludes the free splitting and the dichotomy and nothing metric, and the
injectivity radius follows from neither -- loxodromy is asymptotic and gives no
bound at the first power, and the splitting is not metric.  It is Hull's §5, so
it lives with Hull's family data as
`HullSCFilling.RotatingData.kernel_moves_base`, where the cone-off and its
basepoint are in scope.

**The finite-order lifting clause went second, and it had to** (issue #50).  It
was recorded here as a second conclusion of Theorem 5.3, and
`GGT/DGORotatingQuotientRefutation.lean` proves that the statement carrying it
is **false**: fed a one-point space, where the very rotating condition is
vacuous because its annulus is empty, `DGOQuotientStatement` asserts that for
every group and every normal subgroup every finite-order element of the quotient
lifts to an element of the same order, which `ℤ` modulo the even integers
refutes.  Neither of DGO's own conclusions rescues it --- the one-point model
satisfies the dichotomy, and `GGT/DGOFreeSplittingOnePoint.lean` proves it
satisfies the free splitting 5.3(a) as well, so the route through the
Bass-Serre tree of the splitting cannot reach the clause.  It now lives with the
family Hull builds, as `HullSCFilling.RotatingData.finiteOrder_lift`, where the
stabilisers of the action are known.

What is left is exactly Theorem 5.3(b) together with a quotient that
`ker_eq` and `surjective` pin up to isomorphism, and
`GGT/DGORotatingQuotientResidual.lean` proves that the quotient itself is free:
`G ⧸ ⟨⟨Rot⟩⟩` supplies every field but the dichotomy.

The dichotomy is for the elements of `K` other than `1`, and that restriction is
forced: `not_rotation_or_loxodromic_of_empty` above refutes the unrestricted
form.  `eq_one_of_dist_lt_everywhere`, which refuted the displacement clause
stated at every point, now applies to the clause in its new home. -/
structure RotatingQuotient (C : Set X) (Rot : X → Subgroup G) where
  /-- The quotient group `G / K`. -/
  Q : Type u
  /-- Its group structure. -/
  [group : Group Q]
  /-- The quotient map. -/
  q : G →* Q
  /-- The quotient map is onto. -/
  surjective : Function.Surjective q
  /-- Its kernel is the subgroup generated by the rotations. -/
  ker_eq : q.ker = rotationNormalClosure C Rot
  /-- A nonidentity element of the kernel is a rotation up to conjugacy, or
  loxodromic.  The identity has to be excluded: see
  `not_rotation_or_loxodromic_of_empty`. -/
  rotation_or_loxodromic : ∀ g ∈ rotationNormalClosure C Rot, g ≠ 1 →
    (∃ (a : G) (c : X), c ∈ C ∧ a⁻¹ * g * a ∈ Rot c) ∨
      ∀ x : X, IsLoxodromic g x

instance instGroupRotatingQuotient {C : Set X} {Rot : X → Subgroup G}
    (D : RotatingQuotient C Rot) : Group D.Q := D.group

/-- **A finite-order element of the kernel is conjugate into a rotation
subgroup.**

This is the dichotomy 5.3(b) with the loxodromic branch excluded: a loxodromic
element has infinite order.  It is the first step of the finite-order lifting
clause, and it is the reason the dichotomy is not dead weight -- an earlier
audit in `GGT/HullSCDGO.lean` recorded it as unconsumed, having checked only
the consumers that existed at the time. -/
theorem conj_into_rot_of_isOfFinOrder {C : Set X} {Rot : X → Subgroup G}
    (D : RotatingQuotient C Rot) (x : X) {g : G}
    (hmem : g ∈ rotationNormalClosure C Rot) (hg1 : g ≠ 1)
    (hfin : IsOfFinOrder g) :
    ∃ (a : G) (c : X), c ∈ C ∧ a⁻¹ * g * a ∈ Rot c := by
  rcases D.rotation_or_loxodromic g hmem hg1 with h | h
  · exact h
  · exact absurd hfin (not_isOfFinOrder_of_isLoxodromic (h x))

/-- **The quotient by a very rotating family of a torsion-free group is
torsion-free** --- *given the lifting clause*, which is the hypothesis `hlift`
and is **not** part of `RotatingQuotient` any more.

That hypothesis cannot be dropped, and the reason is issue #50 rather than a
gap in this proof: `GGT/DGORotatingQuotientRefutation.lean` exhibits a
separated very rotating family on a hyperbolic geodesic space with `G`
torsion-free and `G / K` of order two, so torsion-freeness of the quotient does
not follow from the rotating hypotheses at all.  It is Hull's §5 that supplies
the lift, through `HullSCFilling.RotatingData.finiteOrder_lift`. -/
theorem torsionFree_of_rotatingQuotient {C : Set X}
    {Rot : X → Subgroup G}
    (hG : IsPowerTorsionFree G) (D : RotatingQuotient C Rot)
    (hlift : ∀ y : D.Q, IsOfFinOrder y →
      ∃ g : G, D.q g = y ∧ orderOf g = orderOf y) :
    IsPowerTorsionFree D.Q :=
  torsionFree_of_finiteOrder_lift hG D.q hlift

end Family

/-! ## DGO's Theorem 5.3, as a citation, and its consumer -/

/-- **DGO, Theorem 5.3.**  A separated very rotating family on a hyperbolic
space, for an action by isometries, has a quotient with the properties recorded
in `RotatingQuotient`.

This is a citation.  It is the theorem the whole of Hull's §5 -- and therefore
the whole of `HullSC.HullOneStepStatement` -- rests on: the cone-off of the
Cayley graph is hyperbolic, the conjugates of the small cancellation word form
a separated very rotating family on it, and the Greendlinger-type lemmas of
DGO §5 give the clauses above. -/
def DGOQuotientStatement : Prop :=
  ∀ {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (δ ρ : ℝ) (C : Set X) (Rot : X → Subgroup G),
      0 < δ → 200 * δ ≤ ρ → IsHyperbolicSpace δ X →
        IsRotatingFamily G X C Rot → IsSeparated C ρ →
          IsVeryRotating G X δ C Rot → Nonempty (RotatingQuotient C Rot)

/-- The consumer of `DGOQuotientStatement`: from DGO's theorem and the lifting
clause, a separated very rotating family on a torsion-free group has a
torsion-free quotient by the rotations, and that quotient's kernel is exactly
the subgroup the rotations generate.

`hlift` is a hypothesis and not a consequence.  It is the clause that left
`RotatingQuotient` at issue #50, stated here in the form the family data
supplies it (`HullSCFilling.RotatingData.finiteOrder_lift`): for any quotient
map with the right kernel.  Without it the conclusion is false --- the model of
`GGT/DGORotatingQuotientRefutation.lean` is a separated very rotating family on
a hyperbolic geodesic space with `G = ℤ` and `G / K` of order two. -/
theorem torsionFree_of_dgoQuotient (hDGO : DGOQuotientStatement.{u, v})
    {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    {δ ρ : ℝ} {C : Set X} {Rot : X → Subgroup G} (hδ : 0 < δ)
    (hρ : 200 * δ ≤ ρ) (hhyp : IsHyperbolicSpace δ X)
    (hfam : IsRotatingFamily G X C Rot) (hsep : IsSeparated C ρ)
    (hvr : IsVeryRotating G X δ C Rot) (hG : IsPowerTorsionFree G)
    (hlift : ∀ {Q : Type u} [Group Q] (q : G →* Q),
      Function.Surjective q → q.ker = rotationNormalClosure C Rot →
        ∀ y : Q, IsOfFinOrder y → ∃ g : G, q g = y ∧ orderOf g = orderOf y) :
    ∃ (Q : Type u) (_ : Group Q) (q : G →* Q), Function.Surjective q ∧
      q.ker = rotationNormalClosure C Rot ∧ IsPowerTorsionFree Q := by
  obtain ⟨D⟩ := hDGO δ ρ C Rot hδ hρ hhyp hfam hsep hvr
  exact ⟨D.Q, D.group, D.q, D.surjective, D.ker_eq,
    torsionFree_of_rotatingQuotient hG D
      (hlift D.q D.surjective D.ker_eq)⟩

end HullSC
end GroupApproximation
