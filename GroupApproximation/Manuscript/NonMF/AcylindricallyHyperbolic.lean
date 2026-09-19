import GroupApproximation.Sofic.HullSuitabilityGeometry
import GroupApproximation.Algebra.WordMetric

/-!
# The Cayley graph `Γ(G,A)`, acylindrical hyperbolicity, and Hull's suitability

This module supplies the vocabulary of the preamble to the section *"A
torsion-free group with full MF radical"* of `non_mf_groups_exist.tex`:

> For an acylindrically hyperbolic group `G`, choose the generating set `A`
> provided by Hull [Theorem 3.12].  A subgroup is *suitable* if it acts
> non-elementarily on `Γ(G,A)` and normalizes no nontrivial finite
> subgroup [Definition 1.4].

Almost all of the geometry is already in the repository and is **reused**, not
restated.  `Sofic/HullSuitabilityGeometry.lean` writes down Gromov's four-point
condition (`HullGeometry.IsHyperbolicSpace`), Osin's acylindricity condition
(`HullGeometry.IsAcylindrical`), loxodromy and independence
(`HullGeometry.IsLoxodromic`, `HullGeometry.Independent`), non-elementarity
(`HullGeometry.ActsNonElementarily`, i.e. *contains two independent loxodromic
elements*), and Hull's Definition 1.4 in full
(`HullGeometry.IsSuitable`); `Sofic/HullSuitableDefectSubgroup.lean` writes down
its third clause (`HullSuitable.NormalizesNoNontrivialFinite`) and Osin's
`s`-normality (`HullSuitable.IsSNormal`).  `Algebra/WordMetric.lean` supplies the
word metric `d_A(x,y) = |x⁻¹y|_A` of an arbitrary — in particular an infinite —
symmetric generating set.

What is genuinely missing, and is what this module adds, is the **space the
manuscript names**: the Cayley graph `Γ(G,A)` itself, as a metric space carrying
the translation action of `G`.  Everything else here is assembly.

## The definitions

* `Alphabet G` — a symmetric generating set, possibly infinite.  Hull's `A`.
* `Cayley A` — the vertex set of `Γ(G,A)`, a copy of `G`, with the word metric
  of `A` as its pseudometric and left translation as the `G`-action.  Only the
  vertex set is needed: the manuscript's uses of `Γ(G,A)` — hyperbolicity,
  acylindricity, non-elementarity — are all statements about the vertex metric.
* `IsAcylindricallyHyperbolic G` — Osin's definition, in the Cayley-graph
  formulation: some generating set `A` makes `Γ(G,A)` hyperbolic, makes the
  translation action acylindrical, and leaves `G` itself non-elementary.
* `HullGeneratingSet G` — that data, bundled.  This is the manuscript's *"the
  generating set `A` provided by Hull [Theorem 3.12]"*.  With the Cayley-graph
  formulation taken as the definition, Hull's Theorem 3.12 is exactly what
  identifies it with Osin's abstract formulation (a non-elementary acylindrical
  action on *some* hyperbolic space), and the manuscript's *choice* of `A` is
  then unpacking: `exists_hullGeneratingSet` below is proved, not assumed.
* `Suitable A N` — Hull's Definition 1.4, verbatim: `N` acts non-elementarily
  on `Γ(G,A)` and normalizes no nontrivial finite subgroup.

`Suitable.toIsSuitable` checks that this is the same predicate as the repository's
`HullGeometry.IsSuitable` specialised to the Cayley graph, so nothing weaker has
been substituted for Hull's hypothesis.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFree

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric

universe u

/-! ## The Cayley graph as a metric space -/

/-- **An alphabet**: a symmetric generating set of `G`, not required to be
finite.  Hull's Theorem 3.12 produces an infinite one in general, which is why
`Algebra/WordMetric.lean`'s development over an arbitrary `S : Set G` — rather
than `Algebra/HyperbolicGroup.lean`'s `S : Finset G` — is the one used here. -/
structure Alphabet (G : Type u) [Group G] where
  /-- The letters. -/
  carrier : Set G
  /-- The letters are closed under inversion and generate `G`. -/
  symmetricGenerating : IsSymmetricGeneratingSet carrier

/-- **The Cayley graph `Γ(G,A)`**, as the manuscript uses it: its vertex set is
`G`, its metric is the word metric of `A`, and `G` acts on it by left
translation.  Edges are not needed — every statement the manuscript makes about
`Γ(G,A)` is a statement about the vertex metric — so the carrier is a type
synonym for `G` carrying the `A`-dependent pseudometric. -/
def Cayley {G : Type u} [Group G] (_A : Alphabet G) : Type u := G

/-- The vertex of `Γ(G,A)` named by a group element. -/
def Cayley.of {G : Type u} [Group G] (A : Alphabet G) (g : G) : Cayley A := g

/-- The group element naming a vertex of `Γ(G,A)`. -/
def Cayley.val {G : Type u} [Group G] {A : Alphabet G} (x : Cayley A) : G := x

@[simp] theorem Cayley.val_of {G : Type u} [Group G] (A : Alphabet G) (g : G) :
    Cayley.val (Cayley.of A g) = g := rfl

@[simp] theorem Cayley.of_val {G : Type u} [Group G] {A : Alphabet G}
    (x : Cayley A) : Cayley.of A (Cayley.val x) = x := rfl

/-- **The vertex metric of `Γ(G,A)`** is the word metric of `A`.  Symmetry of
the alphabet is what makes it symmetric, and subadditivity of the word length is
the triangle inequality; both are `Algebra/WordMetric.lean`. -/
noncomputable instance instPseudoMetricSpaceCayley {G : Type u} [Group G]
    (A : Alphabet G) : PseudoMetricSpace (Cayley A) where
  dist x y := (wordDist A.carrier (Cayley.val x) (Cayley.val y) : ℝ)
  dist_self x := by
    show ((wordDist A.carrier (Cayley.val x) (Cayley.val x) : ℕ) : ℝ) = 0
    exact_mod_cast wordDist_self A.carrier (Cayley.val x)
  dist_comm x y := by
    show ((wordDist A.carrier (Cayley.val x) (Cayley.val y) : ℕ) : ℝ)
      = ((wordDist A.carrier (Cayley.val y) (Cayley.val x) : ℕ) : ℝ)
    exact_mod_cast wordDist_comm A.symmetricGenerating (Cayley.val x) (Cayley.val y)
  dist_triangle x y z := by
    show ((wordDist A.carrier (Cayley.val x) (Cayley.val z) : ℕ) : ℝ)
      ≤ ((wordDist A.carrier (Cayley.val x) (Cayley.val y) : ℕ) : ℝ)
        + ((wordDist A.carrier (Cayley.val y) (Cayley.val z) : ℕ) : ℝ)
    exact_mod_cast wordDist_triangle A.symmetricGenerating
      (Cayley.val x) (Cayley.val y) (Cayley.val z)

@[simp] theorem Cayley.dist_eq {G : Type u} [Group G] {A : Alphabet G}
    (x y : Cayley A) :
    dist x y = (wordDist A.carrier (Cayley.val x) (Cayley.val y) : ℝ) := rfl

/-- `G` acts on `Γ(G,A)` by left translation. -/
instance instMulActionCayley {G : Type u} [Group G] (A : Alphabet G) :
    MulAction G (Cayley A) :=
  inferInstanceAs (MulAction G G)

@[simp] theorem Cayley.val_smul {G : Type u} [Group G] {A : Alphabet G} (g : G)
    (x : Cayley A) : Cayley.val (g • x) = g * Cayley.val x := rfl

/-- **The translation action is by isometries.**  This is left invariance of the
word metric, `WordMetric.wordDist_left_invariant`, and it is why the isometry
clause never has to be carried as a hypothesis below. -/
theorem isIsometricAction_cayley {G : Type u} [Group G] (A : Alphabet G) :
    IsIsometricAction G (Cayley A) := by
  intro g x y
  simp only [Cayley.dist_eq, Cayley.val_smul]
  exact_mod_cast wordDist_left_invariant A.carrier g (Cayley.val x) (Cayley.val y)

/-- **The basepoint of `Γ(G,A)`**: the identity vertex.  Non-elementarity of a
subgroup is a basepoint-free notion — `HullGeometry.independent_of_independent`
and `HullGeometry.isLoxodromic_of_isLoxodromic` move both clauses between
basepoints — so a single canonical choice suffices. -/
def Cayley.base {G : Type u} [Group G] (A : Alphabet G) : Cayley A :=
  Cayley.of A 1

@[simp] theorem Cayley.val_base {G : Type u} [Group G] (A : Alphabet G) :
    Cayley.val (Cayley.base A) = 1 := rfl

/-- **"Given a finite set `F ⊆ G`, choose a ball in `Γ(G,A)` containing `F`."**

This is the first clause of the manuscript's reduction of Hull's published
injectivity-radius formulation to the finite-set formulation recorded as
`thm:hull`: a finite subset of `G` lies in a ball of `Γ(G,A)` about the
basepoint, at radius the largest of its word lengths.  The second clause —
applying Hull's formulation at that radius — is what the citation
`HullInputs.smallCancellation` carries, and it is a citation rather than a
proof. -/
theorem exists_ball_containing {G : Type u} [Group G] (A : Alphabet G)
    {F : Set G} (hF : F.Finite) :
    ∃ R : ℕ, ∀ x ∈ F, dist (Cayley.base A) (Cayley.of A x) ≤ (R : ℝ) := by
  obtain ⟨R, hR⟩ := (hF.image fun x : G => wordDist A.carrier 1 x).bddAbove
  refine ⟨R, fun x hx => ?_⟩
  have hle : wordDist A.carrier 1 x ≤ R := hR ⟨x, hx, rfl⟩
  simp only [Cayley.dist_eq, Cayley.val_base, Cayley.val_of]
  exact_mod_cast hle

/-! ## Acylindrical hyperbolicity -/

/-- **An acylindrically hyperbolic group** (Osin), in the Cayley-graph
formulation: there is a generating set `A` — possibly infinite — such that
`Γ(G,A)` is hyperbolic, the translation action of `G` on `Γ(G,A)` is
acylindrical, and `G` acts non-elementarily, i.e. contains two independent
loxodromic elements.

The isometry clause is absent because it is a theorem here
(`isIsometricAction_cayley`) rather than a hypothesis. -/
class IsAcylindricallyHyperbolic (G : Type u) [Group G] : Prop where
  /-- Some alphabet makes the Cayley graph hyperbolic and the action
  acylindrical and non-elementary. -/
  out : ∃ (A : Alphabet G) (δ : ℝ),
    IsHyperbolicSpace δ (Cayley A) ∧
      IsAcylindrical G (Cayley A) ∧
        ActsNonElementarily (⊤ : Subgroup G) (Cayley.base A)

/-- **The generating set `A` of the manuscript's preamble** — *"choose the
generating set `A` provided by Hull [Theorem 3.12]"* — bundled with the three
properties Hull's theorem supplies for it. -/
structure HullGeneratingSet (G : Type u) [Group G] where
  /-- Hull's alphabet `A`. -/
  alphabet : Alphabet G
  /-- The hyperbolicity constant of `Γ(G,A)`. -/
  delta : ℝ
  /-- `Γ(G,A)` is hyperbolic. -/
  hyperbolic : IsHyperbolicSpace delta (Cayley alphabet)
  /-- The translation action on `Γ(G,A)` is acylindrical. -/
  acylindrical : IsAcylindrical G (Cayley alphabet)
  /-- `G` acts non-elementarily on `Γ(G,A)`. -/
  nonElementary : ActsNonElementarily (⊤ : Subgroup G) (Cayley.base alphabet)

namespace HullGeneratingSet

variable {G : Type u} [Group G] (A : HullGeneratingSet G)

/-- The translation action on Hull's Cayley graph is by isometries. -/
theorem isometric : IsIsometricAction G (Cayley A.alphabet) :=
  isIsometricAction_cayley A.alphabet

end HullGeneratingSet

/-- **Hull's Theorem 3.12, as the manuscript uses it.**  An acylindrically
hyperbolic group has a generating set `A` with `Γ(G,A)` hyperbolic, the action
acylindrical, and `G` non-elementary.

Because acylindrical hyperbolicity is taken above in its Cayley-graph form, this
is unpacking rather than a citation: Hull's Theorem 3.12 is the theorem that the
Cayley-graph form and Osin's abstract form (a non-elementary acylindrical action
on *some* hyperbolic space) define the same class of groups, and it is that
identification, not the choice of `A`, which is the literature input.  Stating
the definition in the form the manuscript consumes keeps the citation out of the
proof graph entirely. -/
theorem exists_hullGeneratingSet (G : Type u) [Group G]
    [h : IsAcylindricallyHyperbolic G] : Nonempty (HullGeneratingSet G) := by
  obtain ⟨A, δ, hδ, hacy, hne⟩ := h.out
  exact ⟨⟨A, δ, hδ, hacy, hne⟩⟩

/-- The manuscript's chosen `A`, as a term. -/
noncomputable def hullGeneratingSet (G : Type u) [Group G]
    [IsAcylindricallyHyperbolic G] : HullGeneratingSet G :=
  (exists_hullGeneratingSet G).some

/-! ## Hull's Definition 1.4 -/

/-- **Hull, Definition 1.4.**  *"A subgroup is suitable if it acts
non-elementarily on `Γ(G,A)` and normalizes no nontrivial finite subgroup."*

Both clauses are the repository's existing predicates:
`HullGeometry.ActsNonElementarily` (contains two independent loxodromics) and
`HullSuitable.NormalizesNoNontrivialFinite` (every finite subgroup normalized by
`N` is trivial). -/
def Suitable {G : Type u} [Group G] (A : Alphabet G) (N : Subgroup G) : Prop :=
  ActsNonElementarily N (Cayley.base A) ∧
    HullSuitable.NormalizesNoNontrivialFinite N

namespace Suitable

variable {G : Type u} [Group G] {A : Alphabet G} {N : Subgroup G}

/-- The first clause of Hull's Definition 1.4. -/
theorem actsNonElementarily (h : Suitable A N) :
    ActsNonElementarily N (Cayley.base A) := h.1

/-- The third clause of Hull's Definition 1.4. -/
theorem normalizesNoNontrivialFinite (h : Suitable A N) :
    HullSuitable.NormalizesNoNontrivialFinite N := h.2

end Suitable

/-- **`Suitable` is Hull's Definition 1.4, in full.**  Against Hull's alphabet
the two clauses above, together with the properties `A` already carries, are
exactly the five fields of the repository's `HullGeometry.IsSuitable`.  Nothing
weaker has been substituted for Hull's hypothesis. -/
theorem Suitable.toIsSuitable {G : Type u} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (h : Suitable A.alphabet N) :
    IsSuitable A.delta N (Cayley.base A.alphabet) :=
  ⟨A.isometric, A.hyperbolic, A.acylindrical, h.1, h.2⟩

/-- A suitable subgroup is nontrivial, and its elements of infinite order are
what make it so.  Recorded because `HullGeometry.IsSuitable.ne_bot` is stated
for the bundled predicate and the saturation proof consumes the unbundled
one. -/
theorem Suitable.ne_bot {G : Type u} [Group G] (A : HullGeneratingSet G)
    {N : Subgroup G} (h : Suitable A.alphabet N) : N ≠ ⊥ :=
  (h.toIsSuitable A).ne_bot

end TorsionFree
end NonMF
end Manuscript
end GroupApproximation
