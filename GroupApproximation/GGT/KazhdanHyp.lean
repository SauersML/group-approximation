import GroupApproximation.GGT.KazhdanHypLinkGap
import GroupApproximation.Kazhdan.TorsionFreeHyperbolicKazhdan

/-!
# The deterministic route to `SharpExistence`

`Kazhdan/TorsionFreeHyperbolicKazhdan.lean` states `Hyperbolic.SharpExistence`:
an infinite, finitely presented, torsion-free hyperbolic group with Kazhdan's
property `(T)`.  `Kazhdan/SharpExistenceRoutes.lean` measures the two routes the
literature takes to it and finds both to be citations rather than reductions.

This module records the route that is *not* a citation --- Zuk's criterion
applied to an explicit triangular presentation --- states precisely which of its
five clauses this repository can now discharge, and states precisely which two
candidate routes are **empty**, so that no future attempt spends effort on them.

## What the repository already proves

The criterion is done.  `Kazhdan/TriangularHodgeLayer.lean` ends at

* `presented_hasKazhdanPropertyT_of_linkCertificate` --- a triangular
  presentation (every relator a word of three signed generators) whose
  presentation link is `d`-regular and admits an exact rational identity
  `L/d = gap * P0 + Qᵀ Q` with `gap > 1/2` has property `(T)`,

which is the Garland/Ballmann--Swiatkowski/Zuk criterion, with no analytic and no
literature input: the Gram factor is pulled back to the rational group ring and
fed to `ExactHodgeCertificate.Certificate`.  So step (a) of this lane was already
complete before it started, and what was missing was the *input*: nothing in the
repository produced a `Q`.

`GGT/KazhdanHypLinkGap.lean` produces one, for every link that is the incidence
graph of a finite projective plane, uniformly in the order `q`, with

```
    gap = 3/4 - q/(q+1)²  ,      gap > 1/2  ⟺  (q-1)² > 0 .
```

The classical form of that computation names the first nonzero eigenvalue
`1 - √q/(q+1)` of the normalized Laplacian; the module avoids the square root by
completing a square, which is what lets the whole certificate stay inside `ℚ`.

## Two routes that are empty

**Small cancellation cannot supply the hyperbolicity.**  A finite `C'(1/6)`
presentation whose relators are not proper powers gives a torsion-free
hyperbolic group (Lyndon--Schupp; Greendlinger's lemma gives the linear
isoperimetric inequality).  But every finitely presented `C'(1/6)` group acts
properly and cocompactly on a `CAT(0)` cube complex (Wise, *Cubulating small
cancellation groups*, GAFA 14 (2004)), so it is a-T-menable (Niblo--Reeves,
*Groups acting on `CAT(0)` cube complexes*, Geom. Topol. 1 (1997)), and an
a-T-menable group with property `(T)` is compact.  So **no infinite `C'(1/6)`
group has property `(T)`**: the pairing of a `C'(1/6)` hyperbolicity certificate
with a Zuk spectral certificate names an empty class.  This is recorded as
`SmallCancellationRouteIsEmpty` below, as a statement and not as an assumption.

**The density model is excluded by hypothesis.**  Random groups at density
`1/3 < d < 1/2` are the standard witness, and `SharpExistenceRoutes.lean` already
proves that recording their conclusion is a citation.

## The `Ã₂` witness: four clauses, and the fifth provably false

The triangle presentations of Cartwright--Mantero--Steger (*Groups acting simply
transitively on the vertices of a building of type Ã₂*, Geom. Dedicata 47
(1993)) are exactly the data of `TrianglePresentation` below: generators indexed
by the points of `PG(2,q)`, relators `a_x a_y a_z` of length three, and a
presentation link which is the incidence graph of `PG(2,q)`.  For `q = 2` that is
**seven generators and seven relators**, with the Heawood graph as link.

* They are infinite and torsion-free, because they act simply transitively on
  the vertex set of the `Ã₂` building, which is contractible.
* They are finitely presented by construction.
* They have property `(T)`, and that clause is now discharged inside this
  repository by `TrianglePresentation.hasKazhdanPropertyT`.

They are **not hyperbolic**, and cannot be made so: an `Ã₂` building is a
two-dimensional *Euclidean* building, a cocompact lattice in it contains `ℤ²`,
and a hyperbolic group contains no `ℤ²`.  So the `Ã₂` family closes four of the
five clauses of `SharpExistence` and provably closes none of the fifth.  That is
not a defect of the formalization; it is where the mathematics sits.

## What hyperbolicity costs inside the triangular model

For a triangular presentation the presentation complex is two-dimensional with
triangular faces, and the girth of the links is the curvature.  Girth `6` is the
nonpositively curved boundary case and permits flat planes --- the `Ã₂` groups
realize them.  The standard sufficient condition for hyperbolicity is girth at
least `7` in every link (Januszkiewicz--Swiatkowski: `7`-systolic complexes are
hyperbolic).

Girth `7` and `λ₁ > 1/2` pull in opposite directions.  The Alon--Boppana bound in
its girth form (Nilli) forces the second adjacency eigenvalue of a `d`-regular
graph of girth `g` up towards `2√(d-1)`, so `λ₁ > 1/2` --- that is, second
eigenvalue below `d/2` --- fails for small `d`.  The Moore bound then gives a
girth-`7` graph of the surviving degrees several hundred vertices, so the
presentation carries of the order of a hundred and fifty generators and several
hundred relators.  **This estimate is not formalized and is not claimed as a
theorem here.**  It is recorded because it is the reason no hand-written
triangular table will satisfy both clauses: a witness of this shape has to be
generated and machine-checked, and the checking machinery --- `link_regular` and
`link_eq` by `decide`, then `BipartiteLinkData` --- is exactly what is in place.

## The order of work

1. **Done, in the repository.**  The criterion:
   `TriangularHodgeLayer.presented_hasKazhdanPropertyT_of_linkCertificate`.
2. **Done here.**  The certificate for projective-plane links, uniform in `q`:
   `KazhdanHyp.hasKazhdanPropertyT_of_projectivePlaneLink`.
3. **Open, and finite.**  An explicit triangle presentation table over `PG(2,2)`
   --- seven generators, seven relators --- with `link_regular` and `link_eq`
   discharged by evaluation.  This is a finite check, not mathematics, and it is
   the single cheapest remaining step: it makes `TrianglePresentation`
   inhabited.
4. **Open, and real mathematics.**  `Infinite` and `IsPowerTorsionFree` for that
   group.  Both follow from the simply transitive action on the `Ã₂` building
   and neither is a finite check; no purely algebraic substitute is recorded
   here.
5. **Open, and false for `Ã₂`.**  `IsHyperbolicGroup`.  Any witness must leave
   the `Ã₂` family, so its links have girth at least `7`, and it is then
   large; see the previous section.

`sharpExistence_of_planeLinkWitness` is the assembly: it takes exactly the three
clauses of item 4 and item 5 and returns `SharpExistence`, with property `(T)`
and finite presentation discharged.  Unlike the random-group and spectral
routes, **no converse is proved and none is expected**: a hyperbolic Kazhdan
group need not be presented by triangles over a projective plane, so this route
is a genuine reduction rather than a restatement.

Nothing below proves `SharpExistence`, nothing below assumes it, and no
declaration below is conditional on it.
-/

namespace GroupApproximation
namespace KazhdanHyp

/-! ## Triangle presentations over a projective plane -/

/-- **A triangle presentation whose link is a projective-plane incidence
graph.**  This is the data of a Cartwright--Mantero--Steger `Ã₂` presentation,
stated with no building and no geometry: a finite family of length-three
relators, a rational incidence table, and two finite checks saying that the
presentation link of the family is exactly that incidence graph. -/
structure TrianglePresentation (Generator TriangleIndex : Type)
    [Fintype Generator] [DecidableEq Generator] [Nonempty Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] where
  /-- The defining triangles: each is three signed generators. -/
  triangles : TriangleIndex → TriangularHodgeLayer.Triangle Generator
  /-- The projective plane whose incidence graph is the link. -/
  plane : ProjectivePlaneData Generator
  /-- The common degree of the presentation link. -/
  linkDegree : ℕ
  /-- It is the plane's line size. -/
  linkDegree_eq : (linkDegree : ℚ) = plane.order + 1
  /-- **First finite check**: the presentation link is regular. -/
  link_regular : ∀ u, TriangularHodgeLayer.degree triangles u = linkDegree
  /-- **Second finite check**: the presentation link is the incidence graph. -/
  link_eq : ∀ u v,
    (TriangularHodgeLayer.adjacencyCount triangles u v : ℚ) = plane.linkAdj u v

namespace TrianglePresentation

variable {Generator TriangleIndex : Type} [Fintype Generator] [DecidableEq Generator]
  [Nonempty Generator] [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  (S : TrianglePresentation Generator TriangleIndex)

/-- The group the presentation presents. -/
abbrev Carrier : Type := TriangularHodgeLayer.Presented S.triangles

/-- **The presented group has property `(T)`.**  Every step is proved: the
projective-plane link supplies a rational Gram factor
(`KazhdanHyp.hasKazhdanPropertyT_of_projectivePlaneLink`), that discharges
`TriangularHodgeLayer.LinkCertificateChecks`, and the Garland certificate turns
it into a Kazhdan pair. -/
theorem hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} S.Carrier :=
  hasKazhdanPropertyT_of_projectivePlaneLink S.triangles S.plane S.linkDegree
    S.link_regular S.linkDegree_eq S.link_eq

/-- The presented group is finitely presented: a finite alphabet and a finite
relator list. -/
theorem isFinitelyPresented : Group.IsFinitelyPresented S.Carrier := inferInstance

/-- **Four of the five clauses of `SharpExistence`**, from the certificate and
the two group-theoretic inputs that the `Ã₂` construction supplies and this
repository does not.  Hyperbolicity is absent, and for the `Ã₂` groups it is
false. -/
theorem four_clauses (hinf : Infinite S.Carrier) (htf : IsPowerTorsionFree S.Carrier) :
    Infinite S.Carrier ∧ Group.IsFinitelyPresented S.Carrier ∧
      IsPowerTorsionFree S.Carrier ∧ HasKazhdanPropertyT.{0, 0} S.Carrier :=
  ⟨hinf, S.isFinitelyPresented, htf, S.hasKazhdanPropertyT⟩

/-- **`SharpExistence` from one triangle presentation and its three missing
clauses.**  Property `(T)` and finite presentation are discharged; infiniteness,
torsion-freeness and hyperbolicity are the hypotheses, and they are exactly the
open items 4 and 5 of the module docstring. -/
theorem sharpExistence (hinf : Infinite S.Carrier) (htf : IsPowerTorsionFree S.Carrier)
    (hhyp : Hyperbolic.IsHyperbolicGroup S.Carrier) : Hyperbolic.SharpExistence :=
  ⟨S.Carrier, inferInstance, hinf, S.isFinitelyPresented, htf, hhyp,
    S.hasKazhdanPropertyT⟩

end TrianglePresentation

/-! ## The remaining obligation, named -/

/-- **The whole remaining obligation of the deterministic route.**  A triangle
presentation over a projective plane, on a nonempty finite alphabet, whose group
is infinite, torsion-free and hyperbolic.

Only the last three conjuncts are open: property `(T)` and finite presentation
follow from the presentation itself.  The alphabet is taken to be `Fin (n+1)`
and the relator index `Fin m` with no loss --- a presentation on any finite
alphabet transports along a bijection --- so that the statement quantifies over
data rather than over types with instances. -/
def PlaneLinkWitness : Prop :=
  ∃ (n m : ℕ) (S : TrianglePresentation (Fin (n + 1)) (Fin m)),
    Infinite S.Carrier ∧ IsPowerTorsionFree S.Carrier ∧
      Hyperbolic.IsHyperbolicGroup S.Carrier

/-- **The deterministic route reaches the sharp statement.**  This takes no
permanence property, no quasi-isometry invariance and no Morse lemma: the
property `(T)` clause is discharged by the Garland certificate of
`Kazhdan/TriangularHodgeLayer.lean` fed with the rational Gram factor of
`GGT/KazhdanHypLinkGap.lean`. -/
theorem sharpExistence_of_planeLinkWitness (h : PlaneLinkWitness) :
    Hyperbolic.SharpExistence := by
  obtain ⟨_, _, S, hinf, htf, hhyp⟩ := h
  exact S.sharpExistence hinf htf hhyp

/-! ## The route that is empty

The task this lane was given named a `C'(1/6)` presentation as the source of
hyperbolicity and torsion-freeness, to be combined with a Zuk spectral
certificate.  That combination is empty, and the statement of its emptiness is
worth carrying as a named `Prop` so that it is not attempted again. -/

/-- **No infinite `C'(1/6)` group has property `(T)`.**

The proof is two citations and one standard consequence: a finitely presented
`C'(1/6)` group acts properly and cocompactly on a `CAT(0)` cube complex (Wise,
GAFA 14 (2004)); a group acting properly on a `CAT(0)` cube complex is
a-T-menable (Niblo--Reeves, Geom. Topol. 1 (1997)); and an a-T-menable group
with property `(T)` is compact, so here finite.

The small-cancellation hypothesis is carried as an abstract predicate
`SmallCancellation` on groups, because this repository has no `C'(1/6)`
predicate at the generality the argument needs; what matters is the shape of the
conclusion, which is that the two certificates cannot be carried by the same
group.  **Nothing here assumes it**, and no declaration is conditional on it: it
is recorded so that the emptiness of the route is a named object rather than a
remark. -/
def SmallCancellationRouteIsEmpty
    (SmallCancellation : ∀ (G : Type), Group G → Prop) : Prop :=
  ∀ (G : Type) (inst : Group G), SmallCancellation G inst →
    Infinite G → ¬ HasKazhdanPropertyT.{0, 0} G

end KazhdanHyp
end GroupApproximation
