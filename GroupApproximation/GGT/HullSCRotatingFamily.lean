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

It is **very rotating** when a nontrivial rotation about `c` sends any point of
the annulus `20δ ≤ d(·, c) ≤ 40δ` to the far side of `c`: the Gromov product at
`c` of `x` and `g · y` is at most `5δ`, i.e. every geodesic from `x` to `g · y`
passes close to the apex.  This is DGO's condition in Gromov-product form; the
geometric reading -- *geodesics between annulus points and their rotates go
through the apex* -- is what the condition is for, and
`dist_le_dist_smul_of_veryRotating` below is that reading as an inequality.

## What is proved, and what is stated

Proved: the elementary consequences of the definitions.

* `dist_smul_apex_eq` -- a rotation about `c` preserves distance to `c`.
* `dist_le_dist_smul_of_veryRotating` -- **a nontrivial rotation displaces the
  annulus by twice the radius**: `2 d(x,c) - 10δ ≤ d(x, g·x)`.  This is the
  whole force of the very rotating condition; it is what makes the normal
  closure of the rotations behave like a free product, and what makes the
  quotient map injective on balls.
* `ne_of_veryRotating` -- consequently a nontrivial rotation fixes no point of
  the annulus, when `δ > 0`.
* `eq_of_dist_lt_of_isSeparated` -- two apices closer than `ρ` coincide.
* `eq_one_of_dist_lt_everywhere`, `not_rotation_or_loxodromic_of_empty` -- **two
  refutations**, which is why `RotatingQuotient` has the shape it has.  The
  displacement clause may not be stated at every point of `X`: a nontrivial
  rotation fixes its apex and lies in the kernel, so the unrestricted clause
  forces every rotation subgroup to be trivial.  And the dichotomy for the
  elements of `K` may not include `1`: with no apices, `K` is trivial and its
  one element is neither conjugate into a rotation subgroup nor loxodromic.  So
  the structure carries a basepoint, kept `ρ`-far from the apices by
  `DGOQuotientStatement`, and states the dichotomy for `g ≠ 1`.

Stated and cited, not proved: `DGOQuotientStatement`, DGO's Theorem 5.3.  The
clauses used downstream are recorded -- the kernel, the dichotomy for its
elements, the lifting of finite order, and the injectivity radius -- and its
clause that the normal closure `K = ⟨⟨Rot c : c ∈ C⟩⟩` is the *free product* of
a family of conjugates of the rotation subgroups is not, because nothing above
it consumes the free splitting, and carrying an unconsumed clause would put
weight on a statement no proof checks.

The injectivity radius is the clause Hull's Theorem 5.1 turns into injectivity
on a ball of `Γ(G,A)`; `HullSC.injOn_cayleyBall_of_dist_lt` is that conversion,
and it is proved.

`torsionFree_of_dgoQuotient` is the consumer: over a torsion-free `G` the
quotient by a very rotating family is torsion-free, which is the clause of
Hull's Theorem 5.1 that the torsion-free lane of this repository needs.
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

/-- **A very rotating family** (DGO), in Gromov-product form: for a nontrivial
rotation `g` about an apex `c` and any two points `x`, `y` of the annulus of
radii `20δ` and `40δ` about `c`, the Gromov product of `x` and `g · y` at `c`
is at most `5δ`.

Equivalently, and this is the picture: any geodesic from `x` to `g · y` passes
within `5δ` of the apex, so the rotation cannot be undone by moving inside the
annulus. -/
def IsVeryRotating (G : Type u) (X : Type v) [Group G] [PseudoMetricSpace X]
    [MulAction G X] (δ : ℝ) (C : Set X) (Rot : X → Subgroup G) : Prop :=
  ∀ c ∈ C, ∀ g ∈ Rot c, g ≠ 1 → ∀ x y : X,
    20 * δ ≤ dist x c → dist x c ≤ 40 * δ →
      20 * δ ≤ dist y c → dist y c ≤ 40 * δ →
        gromovProduct x (g • y) c ≤ 5 * δ

/-- **The subgroup generated by the rotations**: the normal closure of every
rotation about every apex.  DGO's Theorem 5.3 is about the quotient by it. -/
def rotationNormalClosure (C : Set X) (Rot : X → Subgroup G) : Subgroup G :=
  Subgroup.normalClosure {g : G | ∃ c ∈ C, g ∈ Rot c}

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
theorem dist_le_dist_smul_of_veryRotating {δ : ℝ} {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) {c : X} (hc : c ∈ C) {g : G}
    (hg : g ∈ Rot c) (hg1 : g ≠ 1) {x : X} (hlow : 20 * δ ≤ dist x c)
    (hhigh : dist x c ≤ 40 * δ) :
    2 * dist x c - 10 * δ ≤ dist x (g • x) := by
  have hprod : gromovProduct x (g • x) c ≤ 5 * δ :=
    hvr c hc g hg hg1 x x hlow hhigh hlow hhigh
  have hrad : dist (g • x) c = dist x c := dist_smul_apex_eq hfam hc hg x
  unfold gromovProduct at hprod
  rw [hrad] at hprod
  linarith

/-- A nontrivial rotation fixes no point of the annulus about its apex. -/
theorem ne_of_veryRotating {δ : ℝ} (hδ : 0 < δ) {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) {c : X} (hc : c ∈ C) {g : G}
    (hg : g ∈ Rot c) (hg1 : g ≠ 1) {x : X} (hlow : 20 * δ ≤ dist x c)
    (hhigh : dist x c ≤ 40 * δ) : g • x ≠ x := by
  intro hfix
  have hdisp := dist_le_dist_smul_of_veryRotating hfam hvr hc hg hg1 hlow hhigh
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
  · exact not_isOfFinOrder_of_isLoxodromic (hlox x) isOfFinOrder_one

/-! ## The quotient of DGO's Theorem 5.3 -/

/-- **The quotient produced by DGO's Theorem 5.3.**  Its fields are the clauses
of that theorem which the small cancellation theory above it consumes:

> Every element of `K = ⟨⟨Rot c : c ∈ C⟩⟩` is either conjugate into some
> `Rot c`, or acts loxodromically on `X`; and every finite subgroup of `G / K`
> is the image of a finite subgroup of `G`.

The second clause is recorded in the element form the rest of this repository
uses -- every element of finite order lifts to an element of the same order --
because that is the form `Saturation.torsionFree_of_finiteOrder_lift` consumes
and the form the manuscript's `thm:hull` prints.

The last two fields are the **injectivity radius**, and they are what Hull's
Theorem 5.1 consumes to get injectivity on a ball.  DGO's estimate is that it
grows with the separation `ρ` of the family, so `ρ` is a parameter of this
structure and `separation_le_injRadius` records the estimate in the only form
used downstream: the radius is at least the separation.  Making `ρ` as large as
one likes is what "take the relator deep enough" does, and it is why the
injectivity radius of Hull's theorem can be prescribed.

**The displacement clause is at a basepoint, not at every point**, and the
dichotomy is for the elements of `K` other than `1`.  Both restrictions are
forced: `eq_one_of_dist_lt_everywhere` and `not_rotation_or_loxodromic_of_empty`
above refute the unrestricted forms.  The basepoint `y₀` is a parameter of the
structure rather than a field of it because the consumer chooses it -- Hull
needs the identity vertex of `Γ(G,A)`, not whatever point DGO's proof would
hand back. -/
structure RotatingQuotient (ρ : ℝ) (C : Set X) (Rot : X → Subgroup G)
    (y₀ : X) where
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
  /-- Finite order lifts, with the order preserved. -/
  finiteOrder_lift :
    ∀ y : Q, IsOfFinOrder y → ∃ g : G, q g = y ∧ orderOf g = orderOf y
  /-- The injectivity radius of the quotient map. -/
  injRadius : ℝ
  /-- It is at least the separation of the family. -/
  separation_le_injRadius : ρ ≤ injRadius
  /-- Nothing that moves the basepoint by less than the injectivity radius is
  killed.  At the apices this is false — `eq_one_of_dist_lt_everywhere` — so it
  is a clause about `y₀`, which `DGOQuotientStatement` keeps `ρ`-far from every
  apex. -/
  ne_one_of_dist_lt : ∀ g : G, g ≠ 1 →
    dist y₀ (g • y₀) < injRadius → q g ≠ 1

instance instGroupRotatingQuotient {ρ : ℝ} {C : Set X} {Rot : X → Subgroup G}
    {y₀ : X} (D : RotatingQuotient ρ C Rot y₀) : Group D.Q := D.group

/-- **The quotient by a very rotating family of a torsion-free group is
torsion-free.**  This is the finite-order clause with the ambient
torsion-freeness, and it is the clause of Hull's Theorem 5.1 that the
torsion-free lane of this repository consumes. -/
theorem torsionFree_of_rotatingQuotient {ρ : ℝ} {C : Set X}
    {Rot : X → Subgroup G} {y₀ : X}
    (hG : IsPowerTorsionFree G) (D : RotatingQuotient ρ C Rot y₀) :
    IsPowerTorsionFree D.Q :=
  torsionFree_of_finiteOrder_lift hG D.q D.finiteOrder_lift

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
    (δ ρ : ℝ) (C : Set X) (Rot : X → Subgroup G) (y₀ : X),
      0 < δ → 200 * δ ≤ ρ → IsHyperbolicSpace δ X →
        IsRotatingFamily G X C Rot → IsSeparated C ρ →
          IsVeryRotating G X δ C Rot → (∀ c ∈ C, ρ ≤ dist y₀ c) →
            Nonempty (RotatingQuotient ρ C Rot y₀)

/-- The consumer of `DGOQuotientStatement`: from DGO's theorem, a separated
very rotating family on a torsion-free group has a torsion-free quotient by the
rotations, and that quotient's kernel is exactly the subgroup the rotations
generate. -/
theorem torsionFree_of_dgoQuotient (hDGO : DGOQuotientStatement.{u, v})
    {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    {δ ρ : ℝ} {C : Set X} {Rot : X → Subgroup G} {y₀ : X} (hδ : 0 < δ)
    (hρ : 200 * δ ≤ ρ) (hhyp : IsHyperbolicSpace δ X)
    (hfam : IsRotatingFamily G X C Rot) (hsep : IsSeparated C ρ)
    (hvr : IsVeryRotating G X δ C Rot) (hfar : ∀ c ∈ C, ρ ≤ dist y₀ c)
    (hG : IsPowerTorsionFree G) :
    ∃ (Q : Type u) (_ : Group Q) (q : G →* Q), Function.Surjective q ∧
      q.ker = rotationNormalClosure C Rot ∧ IsPowerTorsionFree Q := by
  obtain ⟨D⟩ := hDGO δ ρ C Rot y₀ hδ hρ hhyp hfam hsep hvr hfar
  exact ⟨D.Q, D.group, D.q, D.surjective, D.ker_eq,
    torsionFree_of_rotatingQuotient hG D⟩

end HullSC
end GroupApproximation
