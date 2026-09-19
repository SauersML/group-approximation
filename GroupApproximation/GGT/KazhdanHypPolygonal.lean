import GroupApproximation.Kazhdan.TriangularHodgeLayer
import GroupApproximation.Kazhdan.TorsionFreeHyperbolicKazhdan

/-!
# The polygonal route: why `k = 3` is forced, and what the witness must be

This module answers three questions about `Hyperbolic.SharpExistence` and records
the answers as statements rather than as prose:

* for which `k` does `lambda_1(link) > 1/2` give property `(T)` on a complex
  whose faces are `k`-gons;
* what changes in the Garland/Zuk computation of `Kazhdan/TriangularHodgeLayer.lean`
  when the faces are `k`-gons;
* which deterministic hyperbolic Kazhdan witness has the smallest finite
  certificate.

## What the literature actually says

**Ballmann--Swiatkowski, GAFA 7 (1997), Theorem 1 and Corollary 1.**  Their
hypothesis is that `X` is a locally finite two-dimensional **simplicial**
complex with connected links and `kappa(X_v) > 1/2` at every vertex, where
`kappa` is the smallest positive eigenvalue of `Delta f = f - Af` and `Af` is
the mean of `f` over the neighbours.  Corollary 1 is the group statement.
**There is no `k`-gonal version of this theorem**: the criterion is stated for
simplicial complexes only, and the constant `1/2` is attached to that case.

**Ballmann--Swiatkowski, Theorem 3 and Corollary 3.**  In the other direction
they prove that a group acting properly discontinuously on a simply connected
`(4,4)`- or `(6,3)`-complex without a fixed point admits an unbounded function
of negative type, so an infinite such group **does not** satisfy property `(T)`.
In their notation a `(k,l)`-complex has faces with at least `k` sides and links
of girth at least `l`.

**The curvature condition, in their notation.**  A `(k,l)`-complex carries a
complete nonpositively curved length metric as soon as `k*l >= 2*(k+l)`, and the
minimal solutions of that inequality are `(6,3)`, `(4,4)` and `(3,6)` --- the
three Euclidean tilings.  So `k*l > 2*(k+l)`, equivalently `1/k + 1/l < 1/2`, is
exactly the condition under which the regular `k`-gon can be realised
hyperbolically with corner angle `2*pi/l`, the Gromov link condition holds
strictly, and the complex is `CAT(-1)`.  A group acting properly cocompactly is
then hyperbolic by Svarc--Milnor.  `gromovLinkCondition` below is that
inequality, and `gromovLinkCondition_three_eight` checks it for the witness.

Putting the two together: the two smallest polygonal cases beyond triangles,
`(4,4)` and `(6,3)`, are *exactly* the cases Ballmann and Swiatkowski prove have
no property `(T)`.  The polygonal route is not merely unformalized, it is
obstructed at its first two instances.

**Bourdon buildings are excluded.**  `I_{p,q}` is a right-angled Fuchsian
building: its chambers are right-angled hyperbolic `p`-gons and its links are
`K_{q,q}`, so `kappa = 1`, the largest possible value.  That is irrelevant.  For
a right-angled Coxeter system every Coxeter cell of the Davis realization is a
Euclidean cube, so the Davis realization of a right-angled building **is a
`CAT(0)` cube complex**; a group acting properly on a `CAT(0)` cube complex is
a-T-menable (Niblo--Reeves, Geom. Topol. 1 (1997)), and an infinite a-T-menable
group does not have property `(T)`.  So no lattice in a Bourdon building is a
witness, whatever its links do.  This is the same obstruction that killed the
`C'(1/6)` route, arriving by a different road.

**Vdovina's `2k`-gonal presentations are excluded for the same reason.**
*Groups, periodic planes and hyperbolic buildings* (arXiv:math/0307380)
constructs polyhedra with `2k`-gonal faces and prescribed bipartite links; the
faces are even-sided throughout and no property `(T)` statement is made there.

## The one claim in the literature that does not check out

Kangaslampi--Vdovina, *Triangular hyperbolic buildings*, C. R. Acad. Sci. Paris
342 (2006), abstract: "We construct triangular hyperbolic polyhedra whose links
are generalized 4-gons.  The universal cover of such a polyhedron is a hyperbolic
building, whose apartments are hyperbolic planes tessellated by regular triangles
with angles `pi/4`.  The fundamental groups of the polyhedra are hyperbolic,
torsion free, with property (T)."

The first two clauses are exactly the picture above: triangles, links of girth
`8`, corner angle `2*pi/8 = pi/4`, `3*8 > 2*(3+8)`.  The third does not follow
from the criteria that paper cites.  Their polyhedra realise the **smallest
thick** generalized quadrangle, `GQ(2,2)`, whose incidence graph is the
Tutte--Coxeter graph: `3`-regular on `30` vertices with adjacency spectrum
`{3, 2^9, 0^10, (-2)^9, -3}`, so

```
    kappa = 1 - 2/3 = 1/3 < 1/2 .
```

So Ballmann--Swiatkowski Corollary 1 and Zuk's criterion say nothing about
these groups, and thickness `2` is far below any large-thickness building
hypothesis.  **This module does not inherit that property `(T)` claim**, and no
declaration below depends on it.  `tutteCoxeterGap_lt_half` records the
arithmetic that rules the criterion out.

## The witness, and its exact size

Keep the faces triangular --- forced, by everything above --- and push the link
girth from `6` (the Euclidean `A~_2` case, which is Kazhdan but not hyperbolic)
to `8`.  A one-vertex triangular complex with `n` generators and `d`-regular link
has `2n` link vertices and `3F = n*d` faces, so `3` must divide `n*d`.  With the
link the incidence graph of a generalized quadrangle of order `(q,q)`:

```
    n = (q+1)(q^2+1) ,   d = q+1 ,   spectrum of the link  = { ±(q+1), ±√(2q), 0 } ,
    kappa = 1 - √(2q)/(q+1) > 1/2   ⟺   (q-3)^2 > 8   ⟺   q ≥ 7 ,
    3 ∣ n*d = (q+1)^2 (q^2+1) .
```

`q = 7` clears the spectral threshold but fails the divisibility
(`3200 = 64*50` is not divisible by `3`), so the smallest admissible order is
`q = 8`:

```
    n = 9 * 65 = 585 generators ,   F = 585*9/3 = 1755 triangular relators ,
    link = incidence graph of GQ(8,8) : 1170 vertices, 9-regular, girth 8 ,
    kappa = 1 - 4/9 = 5/9 > 1/2 ,   3*8 = 24 > 22 = 2*(3+8) .
```

That is the chosen witness, and `gqEightGeneratorCount`, `gqEightFaceCount`,
`gqEightGap_gt_half` and `gromovLinkCondition_three_eight` pin all four numbers.
Its three certificates are `GQEightKazhdanCertificate`,
`GQEightTorsionFreeCertificate` and `GQEightHyperbolicCertificate` below.

## The smallest explicit presentation, and why it is not the witness

Ballmann--Swiatkowski Theorem 2 and Corollary 2 give a completely explicit
finite presentation.  For a finite group `H` with generating set `S` and
presentation `⟨S, R⟩` whose Cayley graph `L = C(H,S)` has girth at least `6`,
the group

```
    Γ = ⟨ S ∪ {τ} | R ∪ {τ²} ∪ {(sτ)³ : s ∈ S} ⟩
```

acts properly discontinuously and cocompactly on a contractible simplicial
`2`-complex all of whose links are `L`; if moreover `kappa(L) > 1/2` then `Γ` has
property `(T)`, and if the girth is at least `7` then `Γ` is hyperbolic.  One
finite graph certifies both clauses, which is the smallest certificate anyone
has for a hyperbolic Kazhdan group.

`Γ` is nevertheless **not** a `SharpExistence` witness: `τ² = 1` puts an
involution in it by construction.  Recovering torsion-freeness means finding a
torsion-free finite-index subgroup, and `Γ` is not known to be linear, so
Selberg's lemma does not apply; whether every hyperbolic group is virtually
torsion-free is open.  `SmallCancellationRouteIsEmpty` in `GGT/KazhdanHyp.lean`
recorded a route that is empty; `BallmannSwiatkowskiWitnessHasTorsion` records a
route that is not empty but delivers two clauses out of three.

## What changes when the faces are `k`-gons

This is the sharpest part of the answer, and it is visible in the repository's
own algebra rather than in the literature.  `TriangularHodgeLayer` proves
(`sum_adjoint_edgeDifference_mul_edgeDifference`)

```
    ∑_{i ∈ ℤ/3} adj(c i + c (i+1)) * (d i + d (i+1))
        = adj(∑ c) * (∑ d)  +  ∑_i adj(c i) * (d i) ,
```

where `c i` is the `i`-th Fox corner of a relator.  Expanding the left side
gives `2 ∑_i adj(c i) d i` plus the sum over **cyclically adjacent ordered
pairs**, while `adj(∑c)(∑d)` is the sum over **all** ordered pairs.  The
identity holds precisely because in `ℤ/3` every ordered pair of distinct
indices is cyclically adjacent.  For a `k`-gon with `k ≥ 4` it fails,
by exactly

```
    KGonDefect  =  ∑_{i,j : j ≠ i, j ≠ i+1, i ≠ j+1} adj(c i) * (d j) ,
```

which is a sum over non-adjacent corner pairs and has no sign.
`cyclicCornerIdentity_three` proves the `k = 3` identity abstractly and
`kGonDefect_three` proves the defect vanishes there; `KGonCornerIdentity` states
the general identity, which is where a `k`-gonal machine would start.

So `k = 3` is not a limitation of this repository's machine.  It is the point at
which the local three-cycle algebra closes, and it is the same point at which
Ballmann and Swiatkowski state their theorem.

## What a `k`-gonal generalization of `TriangularHodgeLayer` would need

In order, and none of it is present:

1. `Triangle`, `letters`, `relator`, `directedAdjacencyCount`, `degree` and
   `linkLaplacian` re-indexed from `Fin 3` to `Fin k`, with `nextCorner` the
   cyclic successor of `Fin k`.  Mechanical.
2. `boundary_eq_sum_cornerBoundaryCoefficient` for `k` corners.  Mechanical: the
   Fox derivative of a length-`k` word has `k` terms.
3. `cornerPrefix_nextCorner` at the cyclic wrap.  Mechanical.
4. `KGonCornerIdentity` --- the statement below.  This is the first non-mechanical
   step, and it introduces `KGonDefect`.
5. **A bound on `KGonDefect`.**  This is the real content and it does not exist.
   The natural route is the spectral gap of the cycle graph `C_k`: writing the
   corner family as a function on `ℤ/k`, one has
   `‖∑ c‖² ≤ k ∑‖c_i‖² - (k/μ_k) E_face` with `μ_k` the largest eigenvalue of the
   cycle Laplacian, `μ_k = 4` for even `k` and `2 + 2cos(π/k)` for odd `k`, which
   is an equality at `k = 3` where `μ_3 = 3`.  Every step after this one inherits
   a `k`-dependent constant.
6. A re-derivation of `garlandDecomposition` and `garlandGap` with that constant,
   producing a threshold that is **not** `1/2` for `k ≥ 4`.  Ballmann--Swiatkowski
   Corollary 3 shows the threshold cannot simply stay at `1/2`: the `(4,4)` and
   `(6,3)` complexes would otherwise be Kazhdan, and they are not.

`LinkCertificateChecks_kgon` below is the definition that step 6 would have to
discharge, with the threshold left as a parameter exactly because its value for
`k ≥ 4` is not known here.

## What the `GQ(8,8)` link certificate needs

`GGT/KazhdanHypLinkGap.lean` builds the rational Gram factor for links that are
incidence graphs of **projective planes**, where the two-step count is
`∑_u adj u v * adj u v' = q δ(v,v') + [same side]`.  For a generalized
quadrangle the same-side term is the **collinearity** graph rather than the
all-ones matrix, so the completed square needs one more block:

```
    A² = (q+1) I + C ,     C ⪯ (q-1) I  on the doubly-mean-zero subspace,
```

the second being the strongly regular bound for the point graph of `GQ(q,q)`
(parameters `((q+1)(q²+1), q(q+1), q-1, q+1)`, eigenvalues `q(q+1)`, `q-1`,
`-q-1`).  Together they give `A² ⪯ 2q I` there, which is what `√(2q)` means, and
the completed square goes through with `μ` any rational in the interval that
`(q-3)² > 8` opens.  Concretely: one extra row block in `gramRow` whose Gram is
the rational factor of `(q-1) I - C` off the constants.  That is the single
missing piece of algebra, and it is the same shape as the piece already built.
-/

namespace GroupApproximation
namespace KazhdanHyp

/-! ## The three-cycle identity, and its failure for `k`-gons -/

/-- The cyclic successor on the corners of a `k`-gon. -/
def cyclicNext {n : ℕ} [NeZero n] (i : Fin n) : Fin n := i + 1

/-- **The defect of the `k`-gonal corner identity**: the sum over ordered pairs
of corners that are neither equal nor cyclically adjacent.  It is empty exactly
when `k = 3`, which is why the Garland computation closes for triangles and for
nothing else. -/
def KGonDefect {R : Type*} [Ring R] {n : ℕ} [NeZero n]
    (adj : R → R) (c d : Fin n → R) : R :=
  ∑ i, ∑ j, (if j = i ∨ j = cyclicNext i ∨ i = cyclicNext j then 0
    else adj (c i) * d j)

/-- **Every ordered pair of corners of a triangle is equal or cyclically
adjacent.**  Nine cases. -/
theorem three_pairs_adjacent (i j : Fin 3) :
    j = i ∨ j = cyclicNext i ∨ i = cyclicNext j := by
  revert i j
  decide

/-- **The defect vanishes for a triangle.** -/
theorem kGonDefect_three {R : Type*} [Ring R] (adj : R → R) (c d : Fin 3 → R) :
    KGonDefect adj c d = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  exact if_pos (three_pairs_adjacent i j)

theorem cyclicNext_zero : cyclicNext (0 : Fin 3) = 1 := by decide

theorem cyclicNext_one : cyclicNext (1 : Fin 3) = 2 := by decide

theorem cyclicNext_two : cyclicNext (2 : Fin 3) = 0 := by decide

/-- **The three-cycle corner identity**, abstractly.  This is the algebraic
heart of `TriangularHodgeLayer.sum_adjoint_edgeDifference_mul_edgeDifference`,
with the group ring replaced by an arbitrary ring and the adjoint by an
arbitrary additive map: the sum of the three edge energies of a triangle is the
Gram term of the corner sum plus the sum of the three corner energies.

It holds because in `ℤ/3` the cyclically adjacent ordered pairs are exactly the
ordered pairs of distinct indices; `kGonDefect_three` is that fact, and
`KGonCornerIdentity` is what replaces this statement for `k ≥ 4`. -/
theorem cyclicCornerIdentity_three {R : Type*} [Ring R]
    (adj : R → R) (hadj : ∀ x y : R, adj (x + y) = adj x + adj y)
    (c d : Fin 3 → R) :
    ∑ i : Fin 3, adj (c i + c (cyclicNext i)) * (d i + d (cyclicNext i))
      = adj (∑ i, c i) * (∑ i, d i) + ∑ i, adj (c i) * d i := by
  simp only [Fin.sum_univ_three, cyclicNext_zero, cyclicNext_one,
    cyclicNext_two, hadj]
  noncomm_ring

/-- **The `k`-gonal corner identity**, stated and not proved.  For `3 ≤ n` the
sum of the `n` edge energies of an `n`-gon is the Gram term of the corner sum,
plus the corner energies, minus the defect over non-adjacent pairs.

This is step 4 of the list in the module docstring.  It is a statement about a
finite cyclic index set and nothing else; what does not exist is step 5, a bound
on `KGonDefect`. -/
def KGonCornerIdentity : Prop :=
  ∀ (R : Type) (_ : Ring R) (n : ℕ) (_ : NeZero n), 3 ≤ n →
    ∀ (adj : R → R), (∀ x y : R, adj (x + y) = adj x + adj y) →
      ∀ c d : Fin n → R,
        ∑ i, adj (c i + c (cyclicNext i)) * (d i + d (cyclicNext i))
          = adj (∑ i, c i) * (∑ i, d i) + (∑ i, adj (c i) * d i)
            - KGonDefect adj c d

/-! ## The `k`-gonal certificate -/

/-- **The `k`-gonal analogue of `TriangularHodgeLayer.LinkCertificateChecks`.**

The four clauses of the triangular predicate are kept verbatim, stated on the
link table itself rather than on a relator family, and the half-threshold is
replaced by a parameter.  That parameter is the whole point: for `k = 3` it is
`1/2`, by Ballmann--Swiatkowski Corollary 1 and by the repository's own Garland
assembly; for `k ≥ 4` its value is not known here, and Ballmann--Swiatkowski
Corollary 3 shows it cannot remain `1/2`, since the `(4,4)`- and
`(6,3)`-complexes admit no Kazhdan cocompact automorphism group. -/
def LinkCertificateChecks_kgon
    {V : Type} [Fintype V] [DecidableEq V] {Row : Type} [Fintype Row]
    (k : ℕ) (adj : V → V → ℚ) (deg gap threshold : ℚ) (rows : Row → V → ℚ) :
    Prop :=
  3 ≤ k ∧ 0 < deg ∧ threshold < gap ∧
    (∀ v, ∑ u, adj u v = deg) ∧
    (∀ v v', ((if v = v' then deg else 0) - adj v v') / deg
        - gap * ((if v = v' then 1 else 0) - 1 / (Fintype.card V : ℚ))
        - ∑ row, rows row v * rows row v' = 0)

/-- **The `k`-gonal criterion, stated and not proved.**  For which `k` and which
`threshold` does a `k`-gonal link certificate give property `(T)`?

For `k = 3` and `threshold = 1/2` this repository proves it, by
`hasKazhdanPropertyT_of_kgonChecks_three` below.  For `k ≥ 4` it is open here,
and by Ballmann--Swiatkowski Corollary 3 any true statement must exclude the
Euclidean pairs `(4,4)` and `(6,3)`. -/
def KGonCriterion (k : ℕ) (threshold : ℚ) : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (Row : Type) (_ : Fintype Row)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (d : ℕ) (gap : ℚ) (rows : Row → Generator × Bool → ℚ),
    LinkCertificateChecks_kgon k
        (fun u v => (TriangularHodgeLayer.adjacencyCount T u v : ℚ))
        (d : ℚ) gap threshold rows →
      (∀ u, TriangularHodgeLayer.degree T u = d) →
        HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented T)

/-! ## The bridge, proved at `k = 3` -/

/-- **A `k`-gonal certificate at `k = 3` is the repository's link certificate.**
The four clauses match one for one; the only work is the cast from the integral
link Laplacian to `ℚ`. -/
theorem linkCertificateChecks_of_kgonChecks_three
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {Row : Type} [Fintype Row]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (d : ℕ) (gap : ℚ) (rows : Row → Generator × Bool → ℚ)
    (hdeg : ∀ u, TriangularHodgeLayer.degree T u = d)
    (h : LinkCertificateChecks_kgon 3
      (fun u v => (TriangularHodgeLayer.adjacencyCount T u v : ℚ))
      (d : ℚ) gap (1 / 2) rows) :
    TriangularHodgeLayer.LinkCertificateChecks T d gap rows := by
  classical
  obtain ⟨-, hdpos, hgap, -, hres⟩ := h
  have hdnat : 0 < d := by exact_mod_cast hdpos
  have hlap : ∀ u v, TriangularHodgeLayer.rationalLinkLaplacian T u v
      = (if u = v then (d : ℚ) else 0)
        - ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ) := by
    intro u v
    have h1 : TriangularHodgeLayer.rationalLinkLaplacian T u v
        = (if u = v then ((TriangularHodgeLayer.degree T u : ℕ) : ℚ) else 0)
          - ((TriangularHodgeLayer.adjacencyCount T u v : ℕ) : ℚ) := by
      simp only [TriangularHodgeLayer.rationalLinkLaplacian,
        TriangularHodgeLayer.linkLaplacian]
      push_cast [apply_ite (fun z : ℤ => (z : ℚ))]
      rfl
    rw [h1, hdeg u]
  refine ⟨hdnat, hgap, hdeg, ?_⟩
  intro u v
  have hr := hres u v
  simp only [TriangularHodgeLayer.linkGapResidual,
    TriangularHodgeLayer.meanZeroProjector, TriangularHodgeLayer.gramMatrix,
    hlap u v]
  exact hr

/-- **The `k`-gonal criterion holds at `k = 3` with threshold `1/2`.**  This is
the Ballmann--Swiatkowski/Zuk criterion as this repository has it, restated in
the `k`-gonal vocabulary so that the gap between `k = 3` and `k ≥ 4` is a
statement about one numeral. -/
theorem hasKazhdanPropertyT_of_kgonChecks_three
    {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
    [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    {Row : Type} [Fintype Row]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (d : ℕ) (gap : ℚ) (rows : Row → Generator × Bool → ℚ)
    (hdeg : ∀ u, TriangularHodgeLayer.degree T u = d)
    (h : LinkCertificateChecks_kgon 3
      (fun u v => (TriangularHodgeLayer.adjacencyCount T u v : ℚ))
      (d : ℚ) gap (1 / 2) rows) :
    HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented T) :=
  TriangularHodgeLayer.presented_hasKazhdanPropertyT_of_linkCertificate T d gap
    rows (linkCertificateChecks_of_kgonChecks_three T d gap rows hdeg h)

/-- **`KGonCriterion 3 (1/2)` is a theorem.**  The `k = 3` instance of the open
statement, discharged. -/
theorem kGonCriterion_three : KGonCriterion 3 (1 / 2) := by
  intro Generator TriangleIndex _ _ _ _ _ Row _ T d gap rows h hdeg
  exact hasKazhdanPropertyT_of_kgonChecks_three T d gap rows hdeg h

/-! ## The curvature condition -/

/-- **The Gromov link condition for a `(k,l)`-complex**, in the form
Ballmann--Swiatkowski use: `k*l > 2*(k+l)`, equivalently `1/k + 1/l < 1/2`.  The
regular `k`-gon is then realisable hyperbolically with corner angle `2*pi/l`, the
link condition holds strictly, and the complex is `CAT(-1)`.  Equality holds
exactly at `(6,3)`, `(4,4)` and `(3,6)`, the Euclidean tilings. -/
def gromovLinkCondition (k l : ℕ) : Prop := 2 * (k + l) < k * l

/-- Triangles with links of girth `8` are strictly negatively curved:
`24 > 22`. -/
theorem gromovLinkCondition_three_eight : gromovLinkCondition 3 8 := by
  unfold gromovLinkCondition
  norm_num

/-- Triangles with links of girth `6` --- the `A~_2` case --- are Euclidean, not
strictly negatively curved.  This is the numeric form of the obstruction that
stopped the `A~_2` witness. -/
theorem not_gromovLinkCondition_three_six : ¬ gromovLinkCondition 3 6 := by
  unfold gromovLinkCondition
  norm_num

/-! ## The arithmetic of the chosen witness -/

/-- The generalized quadrangle `GQ(8,8)` has `585` points and `585` lines, so a
one-vertex triangular complex with that link has `585` generators. -/
theorem gqEightGeneratorCount : (8 + 1) * (8 ^ 2 + 1) = 585 := by norm_num

/-- `3 * F = n * d` with `n = 585` and `d = 9` gives `1755` triangular relators,
and in particular `3` divides `n * d`, which is what makes a one-vertex complex
possible at all. -/
theorem gqEightFaceCount : 585 * 9 = 3 * 1755 := by norm_num

/-- The order-`7` quadrangle clears the spectral threshold but fails the
divisibility `3 ∣ n * d`, which is why the witness is `q = 8` and not `q = 7`:
`400 * 8 = 3200` leaves remainder `2`. -/
theorem gqSevenFaceCountFails : 400 * 8 % 3 = 2 := by norm_num

/-- **The link gap of `GQ(8,8)` clears the half-threshold.**  The incidence graph
is `9`-regular with non-principal adjacency eigenvalues `±4` and `0`, so
`kappa = 1 - 4/9 = 5/9`. -/
theorem gqEightGap_gt_half : (1 : ℚ) / 2 < 1 - 4 / 9 := by norm_num

/-- **The Tutte--Coxeter graph does not clear the half-threshold.**  It is the
incidence graph of the smallest thick generalized quadrangle `GQ(2,2)`,
`3`-regular with non-principal eigenvalues `±2` and `0`, so `kappa = 1/3`.  This
is the arithmetic that rules Zuk's criterion out for the
Kangaslampi--Vdovina polyhedra, so their property `(T)` claim is not inherited
here. -/
theorem tutteCoxeterGap_lt_half : (1 : ℚ) - 2 / 3 < 1 / 2 := by norm_num

/-! ## The three certificates of the witness -/

/-- **Certificate one: property `(T)`.**  A one-vertex triangular presentation
whose link is the incidence graph of `GQ(8,8)`, together with the rational Gram
factor of its normalized link Laplacian above `1/2`.

This is not a residual in the sense the other two are: given the table and the
Gram rows, `hasKazhdanPropertyT_of_kgonChecks_three` discharges it.  What is
missing is the data, and `GQEightLinkGramFactor` names the piece of algebra that
produces it. -/
def GQEightKazhdanCertificate : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
    (∀ u, TriangularHodgeLayer.degree T u = 9) →
      Fintype.card Generator = 585 →
        HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented T)

/-- **The missing algebra behind certificate one.**  The rational Gram factor of
`L/d - gap * P0` for a link that is the incidence graph of a generalized
quadrangle of order `(q,q)`.

`GGT/KazhdanHypLinkGap.lean` builds this factor when the link is the incidence
graph of a projective plane, where the two-step count is
`q * delta + [same side]`.  For a quadrangle the same-side term is the
collinearity graph `C`, and the completed square needs the strongly regular
bound `C ⪯ (q-1) I` off the constants, which turns `A² = (q+1) I + C` into
`A² ⪯ 2q I` and reproduces `√(2q)` without a square root. -/
def GQEightLinkGramFactor : Prop :=
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (adj : V → V → ℚ) (col : V → V → ℚ),
    (∀ v v', ∑ u, adj u v * adj u v' = 9 * (if v = v' then 1 else 0) + col v v') →
      ∃ (Row : Type) (_ : Fintype Row) (rows : Row → V → ℚ),
        ∀ v v', ((if v = v' then (9 : ℚ) else 0) - adj v v') / 9
            - (5 / 9) * ((if v = v' then 1 else 0) - 1 / (Fintype.card V : ℚ))
            - ∑ row, rows row v * rows row v' = 0

/-- **Certificate two: torsion-freeness.**  For a one-vertex triangular complex
the group acts simply transitively on the vertices of the universal cover, and
torsion-freeness is equivalent to the action being free on the whole complex:
an element of finite order fixes a point of the `CAT(0)` cover, so it stabilises
the carrier simplex and permutes its vertices, and a cyclic permutation of a
triangle would give an element of order three.  That is a finite condition on
the triangle table, which is why this clause is cheap for a triangular witness
and was not cheap for any polygonal one. -/
def GQEightTorsionFreeCertificate : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
    (∀ u, TriangularHodgeLayer.degree T u = 9) →
      IsPowerTorsionFree (TriangularHodgeLayer.Presented T)

/-- **Certificate three: hyperbolicity.**  With triangular faces and links of
girth `8` the complex satisfies `gromovLinkCondition 3 8` strictly, carries a
piecewise-hyperbolic `CAT(-1)` metric with corner angle `2*pi/8 = pi/4`, and the
group acts properly cocompactly on it, so it is hyperbolic by Svarc--Milnor.

None of `CAT(-1)`, the Gromov link condition and Svarc--Milnor is available in
this repository, and `Algebra/HyperbolicQuasiIsometry.lean` already records the
Morse-lemma half of the missing geometry.  This is the deepest of the three. -/
def GQEightHyperbolicCertificate : Prop :=
  ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
    (∀ u, TriangularHodgeLayer.degree T u = 9) →
      Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T)

/-- **The existence of the table.**  A one-vertex triangular presentation on
`585` generators whose presentation link is the incidence graph of `GQ(8,8)`.

Kangaslampi and Vdovina construct such tables for the smallest thick quadrangle
`GQ(2,2)`, where the spectral threshold fails; no construction at order `8` is
recorded in the sources consulted here, and the divisibility `3 ∣ 585 * 9` is
only the necessary condition. -/
def GQEightTableExists : Prop :=
  ∃ (Generator TriangleIndex : Type) (_ : Fintype Generator)
    (_ : DecidableEq Generator) (_ : Nonempty Generator)
    (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
    Fintype.card Generator = 585 ∧
      (∀ u, TriangularHodgeLayer.degree T u = 9) ∧
      Infinite (TriangularHodgeLayer.Presented T)

/-! ## The assembly -/

/-- **`SharpExistence` from the three certificates and the table.**  Property
`(T)` and finite presentation are discharged by the machine; the hypotheses are
exactly the three named certificates and the existence of the table. -/
theorem sharpExistence_of_gqEightCertificates
    (htable : GQEightTableExists)
    (hkazhdan : GQEightKazhdanCertificate)
    (htf : GQEightTorsionFreeCertificate)
    (hhyp : GQEightHyperbolicCertificate) :
    Hyperbolic.SharpExistence := by
  obtain ⟨Generator, TriangleIndex, fg, dg, ng, ft, dt, T, hcard, hdeg, hinf⟩ :=
    htable
  exact ⟨TriangularHodgeLayer.Presented T, inferInstance, hinf, inferInstance,
    htf Generator TriangleIndex fg dg ng ft dt T hdeg,
    hhyp Generator TriangleIndex fg dg ng ft dt T hdeg,
    hkazhdan Generator TriangleIndex fg dg ng ft dt T hdeg hcard⟩

/-! ## The route that delivers two clauses out of three -/

/-- **The Ballmann--Swiatkowski witness has torsion.**  Their Theorem 2 presents
`Γ = ⟨S ∪ {τ} | R ∪ {τ²} ∪ {(sτ)³ : s ∈ S}⟩`, which is the smallest explicit
certificate for a hyperbolic Kazhdan group --- one finite Cayley graph of girth
at least `7` with `kappa > 1/2` certifies both clauses --- and `τ² = 1` puts an
involution in it by construction.

Recorded as a statement about any group carrying an involution, so that the
obstruction is a named object.  Nothing here assumes it. -/
def BallmannSwiatkowskiWitnessHasTorsion : Prop :=
  ∀ (G : Type) (_ : Group G) (t : G), t ≠ 1 → t * t = 1 →
    ¬ IsPowerTorsionFree G

/-- The obstruction is immediate: an involution is a power-torsion element. -/
theorem ballmannSwiatkowskiWitnessHasTorsion :
    BallmannSwiatkowskiWitnessHasTorsion := by
  intro G _ t ht hsq htf
  exact ht (htf t 2 (by norm_num) (by rw [pow_two]; exact hsq))

end KazhdanHyp
end GroupApproximation
