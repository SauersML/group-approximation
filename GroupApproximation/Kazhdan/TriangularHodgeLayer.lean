import GroupApproximation.Kazhdan.FoxBoundary
import GroupApproximation.Kazhdan.FiniteSupportHodgeCertificate
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.NumberTheory.SumFourSquares

/-!
# Exact finite link data for triangular presentations

This is the combinatorial front end for an exact Hodge certificate.  A
triangle is three literal signed generators.  From a finite family we build
the directed link adjacency counts and integral link Laplacian.  Independently,
the Fox boundary of every defining triangle is proved to satisfy the chain
equation required by `ExactHodgeCertificate.Certificate`.  All objects are
finite data and all equalities are kernel checked.
-/

namespace GroupApproximation.TriangularHodgeLayer

open ExactHodgeCertificate PresentedGroupRelatorReplay FoxBoundary
open scoped BigOperators MonoidAlgebra

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

abbrev SignedGenerator (Generator : Type) := Generator × Bool
abbrev Triangle (Generator : Type) := Fin 3 → SignedGenerator Generator

def letters (t : Triangle (Generator := Generator)) : SignedWord Generator :=
  List.ofFn t

@[simp] theorem letters_eq_three (t : Triangle (Generator := Generator)) :
    letters t = [t 0, t 1, t 2] := by
  simp [letters, List.ofFn_succ]

def relator (t : Triangle (Generator := Generator)) : FreeGroup Generator :=
  word (letters t)

def relators (T : TriangleIndex → Triangle (Generator := Generator)) :
    Finset (FreeGroup Generator) :=
  Finset.univ.image (relator ∘ T)

abbrev Presented (T : TriangleIndex → Triangle (Generator := Generator)) :=
  PresentedGroup (relators T : Set (FreeGroup Generator))

def generator (T : TriangleIndex → Triangle (Generator := Generator)) :
    Generator → Presented T := PresentedGroup.of

theorem closure_range_presented (R : Set (FreeGroup Generator)) :
    Subgroup.closure (Set.range
      (PresentedGroup.of : Generator → PresentedGroup R)) = ⊤ :=
  PresentedGroup.closure_range_of R

theorem closure_range_generator
    (T : TriangleIndex → Triangle (Generator := Generator)) :
    Subgroup.closure (Set.range (generator T)) = ⊤ := by
  simpa only [generator] using
    (closure_range_presented (Generator := Generator)
      (relators T : Set (FreeGroup Generator)))

theorem relator_mem (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) : relator (T j) ∈ relators T := by
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

noncomputable def boundary
    (T : TriangleIndex → Triangle (Generator := Generator)) :
    TriangleIndex → Generator → RatGroupRing (Presented T) :=
  fun j ↦ FoxBoundary.boundary (generator T) (letters (T j))

theorem wordValue_triangle_eq_one
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) :
    wordValue (generator T) (letters (T j)) = 1 := by
  change wordValue
    (fun i ↦ PresentedGroup.mk (relators T : Set (FreeGroup Generator))
      (FreeGroup.of i)) (letters (T j)) = 1
  rw [wordValue_freeGroup_map]
  exact PresentedGroup.one_of_mem (relator_mem T j)

/-- Every triangular Fox row satisfies the exact chain equation consumed by
the Hodge certificate. -/
theorem boundary_chain
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) :
    ∑ i, boundary T j i * generatorCoboundary (generator T) i = 0 := by
  change (∑ i, FoxBoundary.boundary (generator T) (letters (T j)) i *
    generatorCoboundary (generator T) i) = 0
  rw [FoxBoundary.sum_boundary_mul_coboundary]
  rw [wordValue_triangle_eq_one T j]
  rw [← MonoidAlgebra.one_def]
  exact sub_self 1

/-! ## Literal three-corner expansion of the Fox row -/

/-- Value of one signed corner in the presented group. -/
def cornerValue
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) : Presented T :=
  letterValue (generator T) (T j k)

/-- Prefix immediately before a corner. -/
def cornerPrefix
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) : Fin 3 → Presented T :=
  ![1, cornerValue T j 0, cornerValue T j 0 * cornerValue T j 1]

/-- The contribution of one literal corner to one Fox coordinate. -/
noncomputable def cornerBoundaryCoefficient
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) (i : Generator) :
    RatGroupRing (Presented T) :=
  if i = (T j k).1 then
    if (T j k).2 then MonoidAlgebra.single (cornerPrefix T j k) 1
    else -MonoidAlgebra.single
      (cornerPrefix T j k * cornerValue T j k) 1
  else 0

/-- The three corner values multiply to one in the presented group. -/
theorem cornerValue_mul_cornerValue_mul_cornerValue
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) :
    cornerValue T j 0 * cornerValue T j 1 * cornerValue T j 2 = 1 := by
  rw [mul_assoc]
  simpa [cornerValue, wordValue] using wordValue_triangle_eq_one T j

/-- The recursive Fox boundary is the sum of its three literal corner
contributions. -/
theorem boundary_eq_sum_cornerBoundaryCoefficient
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (i : Generator) :
    boundary T j i = ∑ k : Fin 3, cornerBoundaryCoefficient T j k i := by
  classical
  rcases h0 : T j 0 with ⟨g0, s0⟩
  rcases h1 : T j 1 with ⟨g1, s1⟩
  rcases h2 : T j 2 with ⟨g2, s2⟩
  cases s0 <;> cases s1 <;> cases s2 <;>
    simp [boundary, FoxBoundary.boundary, FoxBoundary.boundaryFrom,
      cornerBoundaryCoefficient, cornerPrefix, cornerValue,
      h0, h1, h2, Fin.sum_univ_succ]

/-! ## The finite undirected link multigraph -/

/-- Cyclic successor among the three corners. -/
def nextCorner (k : Fin 3) : Fin 3 :=
  ⟨(k.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- Inverse of a signed generator. -/
def inverseSigned (u : SignedGenerator (Generator := Generator)) :
    SignedGenerator (Generator := Generator) :=
  (u.1, !u.2)

/-- Exact multiplicity of directed cyclic corners from `u` to `v`. -/
def directedAdjacencyCount
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u v : SignedGenerator (Generator := Generator)) : ℕ :=
  ((Finset.univ : Finset (TriangleIndex × Fin 3)).filter fun p ↦
    T p.1 p.2 = u ∧ inverseSigned (T p.1 (nextCorner p.2)) = v).card

/-- Exact multiplicity of the undirected presentation-link edge `{u,v}`.
A cyclic pair `a b` contributes once from `a` to `b⁻¹` and once in the
transpose entry.  Writing this as a sum, rather than the cardinality of a
disjunction, is essential: a loop or coincident pair contributes twice. -/
def adjacencyCount
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u v : SignedGenerator (Generator := Generator)) : ℕ :=
  directedAdjacencyCount T u v + directedAdjacencyCount T v u

theorem adjacencyCount_comm
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u v : SignedGenerator (Generator := Generator)) :
    adjacencyCount T u v = adjacencyCount T v u := by
  simp [adjacencyCount, add_comm]

/-- A loop has two edge ends, including when both orientations arise from the
same cyclic corner. -/
theorem adjacencyCount_self
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u : SignedGenerator (Generator := Generator)) :
    adjacencyCount T u u = 2 * directedAdjacencyCount T u u := by
  simp [adjacencyCount, two_mul]

/-- Vertex degree, with edge-end multiplicities; a loop counts twice. -/
def degree
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u : SignedGenerator (Generator := Generator)) : ℕ :=
  ∑ v, adjacencyCount T u v

/-- Integral multigraph link Laplacian `D - A`. -/
def linkLaplacian
    (T : TriangleIndex → Triangle (Generator := Generator))
  (u v : SignedGenerator (Generator := Generator)) : ℤ :=
  (if u = v then degree T u else 0) - adjacencyCount T u v

theorem linkLaplacian_comm
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u v : SignedGenerator (Generator := Generator)) :
    linkLaplacian T u v = linkLaplacian T v u := by
  by_cases h : u = v
  · subst v
    rfl
  · have h' : v ≠ u := fun hvu ↦ h hvu.symm
    simp [linkLaplacian, h, h', adjacencyCount_comm]

/-- Every row of the exact link Laplacian sums to zero. -/
theorem linkLaplacian_row_sum
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u : SignedGenerator (Generator := Generator)) :
    ∑ v, linkLaplacian T u v = 0 := by
  classical
  simp [linkLaplacian, degree, Finset.sum_sub_distrib]

/-- Rational form used by exact spectral/Gram computations. -/
def rationalLinkLaplacian
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u v : SignedGenerator (Generator := Generator)) : ℚ :=
  linkLaplacian T u v

theorem rationalLinkLaplacian_row_sum
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u : SignedGenerator (Generator := Generator)) :
    ∑ v, rationalLinkLaplacian T u v = 0 := by
  have h := congrArg (fun z : ℤ ↦ (z : ℚ))
    (linkLaplacian_row_sum T u)
  simpa [rationalLinkLaplacian] using h

/-! ## Pulling signed-link coordinates back to generator coordinates -/

/-- Coefficient of a generator coordinate in the signed-link coordinate.
For an inverse letter it is `1`; for a positive letter it is `-s⁻¹`.
This is the orientation convention for which a link edge coming from two
successive letters has exactly the corresponding Fox cross term. -/
noncomputable def orientedCoefficient
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u : SignedGenerator (Generator := Generator)) (i : Generator) :
    RatGroupRing (Presented T) :=
  if u.1 = i then
    if u.2 then -MonoidAlgebra.single (generator T i)⁻¹ 1 else 1
  else 0

/-- The two orientations above one generator add to minus the adjoint of its
group-ring coboundary.  This is the exact degree-zero term in the Garland
pullback, with no represented-operator or analytic premise. -/
theorem orientedCoefficient_pair_sum
    (T : TriangleIndex → Triangle (Generator := Generator))
    (g i : Generator) :
    orientedCoefficient T (g, false) i +
        orientedCoefficient T (g, true) i =
      if g = i then
        -adjoint (generatorCoboundary (generator T) i)
      else 0 := by
  by_cases h : g = i
  · subst g
    simp [orientedCoefficient, generatorCoboundary, sub_eq_add_neg, add_comm]
  · simp [orientedCoefficient, h]

/-- Summing all signed-link coordinates gives minus the adjoint generator
coboundary. -/
theorem sum_orientedCoefficient
    (T : TriangleIndex → Triangle (Generator := Generator)) (i : Generator) :
    ∑ u : SignedGenerator (Generator := Generator), orientedCoefficient T u i =
      -adjoint (generatorCoboundary (generator T) i) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hpair (g : Generator) :
      orientedCoefficient T (g, true) i +
          orientedCoefficient T (g, false) i =
        if g = i then -adjoint (generatorCoboundary (generator T) i) else 0 := by
    rw [add_comm]
    exact orientedCoefficient_pair_sum T g i
  simp_rw [hpair]
  rw [Fintype.sum_ite_eq']

/-- The two orientations pull back the identity matrix to twice the identity.
This is the second exact normalization used by the `2 * gap - 1` estimate. -/
theorem sum_adjoint_orientedCoefficient_mul
    (T : TriangleIndex → Triangle (Generator := Generator)) (i k : Generator) :
    (∑ u : SignedGenerator (Generator := Generator),
      adjoint (orientedCoefficient T u i) * orientedCoefficient T u k) =
      if i = k then MonoidAlgebra.single 1 2 else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  by_cases h : i = k
  · subst k
    rw [if_pos rfl]
    have hterm (g : Generator) :
        adjoint (orientedCoefficient T (g, true) i) *
              orientedCoefficient T (g, true) i +
            adjoint (orientedCoefficient T (g, false) i) *
              orientedCoefficient T (g, false) i =
          if g = i then MonoidAlgebra.single 1 2 else 0 := by
      by_cases hgi : g = i
      · subst g
        rw [if_pos rfl]
        simp [orientedCoefficient, MonoidAlgebra.one_def,
          ← MonoidAlgebra.single_add] <;> ring
      · simp [orientedCoefficient, hgi]
    simp_rw [hterm]
    rw [Fintype.sum_ite_eq']
  · have h' : k ≠ i := fun hki ↦ h hki.symm
    rw [if_neg h]
    apply Finset.sum_eq_zero
    intro g hg
    by_cases hgi : g = i
    · subst g
      simp [orientedCoefficient, h, h']
    · by_cases hgk : g = k
      · subst g
        simp [orientedCoefficient, h, h']
      · simp [orientedCoefficient, hgi, hgk]

/-- Pullback of one directed link edge to generator coordinates. -/
noncomputable def edgeDifference
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) (i : Generator) :
    RatGroupRing (Presented T) :=
  orientedCoefficient T (T j k) i -
    orientedCoefficient T (inverseSigned (T j (nextCorner k))) i

/-- Unit translating the two adjacent Fox corner terms to the corresponding
signed-link edge difference. -/
noncomputable def edgeTranslationUnit
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) : RatGroupRing (Presented T) :=
  -MonoidAlgebra.single
    (cornerPrefix T j k * cornerValue T j k)⁻¹ 1

/-- Moving to the next corner extends the prefix by the present letter.  At
the cyclic wrap this is exactly the defining triangular relation. -/
theorem cornerPrefix_nextCorner
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) :
    cornerPrefix T j (nextCorner k) =
      cornerPrefix T j k * cornerValue T j k := by
  have hprod := cornerValue_mul_cornerValue_mul_cornerValue T j
  fin_cases k
  · simp [cornerPrefix, nextCorner]
  · simp [cornerPrefix, nextCorner]
  · simpa [cornerPrefix, nextCorner] using hprod.symm

/-- The translating unit sends the current Fox corner to its oriented link
coordinate. -/
theorem edgeTranslationUnit_mul_corner
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) (i : Generator) :
    edgeTranslationUnit T j k * cornerBoundaryCoefficient T j k i =
      orientedCoefficient T (T j k) i := by
  rcases h : T j k with ⟨g, s⟩
  cases s <;> by_cases hi : g = i
  · subst g
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      cornerValue, letterValue, h, MonoidAlgebra.one_def] <;> group
  · have hig : i ≠ g := fun hgi ↦ hi hgi.symm
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      cornerValue, h, hi, hig, MonoidAlgebra.one_def]
  · subst g
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      cornerValue, letterValue, h, MonoidAlgebra.one_def] <;> group
  · have hig : i ≠ g := fun hgi ↦ hi hgi.symm
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      cornerValue, h, hi, hig, MonoidAlgebra.one_def]

/-- The same unit sends the successor Fox corner to minus the coordinate of
the inverse successor letter. -/
theorem edgeTranslationUnit_mul_nextCorner
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) (i : Generator) :
    edgeTranslationUnit T j k *
        cornerBoundaryCoefficient T j (nextCorner k) i =
      -orientedCoefficient T (inverseSigned (T j (nextCorner k))) i := by
  have hp := cornerPrefix_nextCorner T j k
  rcases hcurrent : T j k with ⟨gcurrent, scurrent⟩
  rcases h : T j (nextCorner k) with ⟨g, s⟩
  cases scurrent <;> cases s <;> by_cases hi : g = i
  · subst g
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      inverseSigned, cornerValue, letterValue, hcurrent, h, hp,
      MonoidAlgebra.one_def] <;> group
  · have hig : i ≠ g := fun hgi ↦ hi hgi.symm
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      inverseSigned, cornerValue, hcurrent, h, hi, hig, hp,
      MonoidAlgebra.one_def]
  · subst g
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      inverseSigned, cornerValue, letterValue, hcurrent, h, hp,
      MonoidAlgebra.one_def] <;> group
  · have hig : i ≠ g := fun hgi ↦ hi hgi.symm
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      inverseSigned, cornerValue, hcurrent, h, hi, hig, hp,
      MonoidAlgebra.one_def]
  · subst g
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      inverseSigned, cornerValue, letterValue, hcurrent, h, hp,
      MonoidAlgebra.one_def] <;> group
  · have hig : i ≠ g := fun hgi ↦ hi hgi.symm
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      inverseSigned, cornerValue, hcurrent, h, hi, hig, hp,
      MonoidAlgebra.one_def]
  · subst g
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      inverseSigned, cornerValue, letterValue, hcurrent, h, hp,
      MonoidAlgebra.one_def] <;> group
  · have hig : i ≠ g := fun hgi ↦ hi hgi.symm
    simp [edgeTranslationUnit, cornerBoundaryCoefficient, orientedCoefficient,
      inverseSigned, cornerValue, hcurrent, h, hi, hig, hp,
      MonoidAlgebra.one_def]

/-- Local Garland identity before taking a Gram product: a pulled-back link
edge difference is a unit translate of the sum of its adjacent Fox corners. -/
theorem edgeDifference_eq_translation_mul_corner_sum
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) (i : Generator) :
    edgeDifference T j k i =
      edgeTranslationUnit T j k *
        (cornerBoundaryCoefficient T j k i +
          cornerBoundaryCoefficient T j (nextCorner k) i) := by
  rw [mul_add, edgeTranslationUnit_mul_corner,
    edgeTranslationUnit_mul_nextCorner]
  simp [edgeDifference, sub_eq_add_neg]

/-- The translating coefficient is unitary in the rational group ring. -/
theorem adjoint_edgeTranslationUnit_mul_self
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) :
    adjoint (edgeTranslationUnit T j k) * edgeTranslationUnit T j k = 1 := by
  simp [edgeTranslationUnit, MonoidAlgebra.one_def]

/-- Taking a Gram product removes the translating unit. -/
theorem adjoint_edgeDifference_mul_edgeDifference
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) (i l : Generator) :
    adjoint (edgeDifference T j k i) * edgeDifference T j k l =
      adjoint (cornerBoundaryCoefficient T j k i +
        cornerBoundaryCoefficient T j (nextCorner k) i) *
      (cornerBoundaryCoefficient T j k l +
        cornerBoundaryCoefficient T j (nextCorner k) l) := by
  rw [edgeDifference_eq_translation_mul_corner_sum,
    edgeDifference_eq_translation_mul_corner_sum]
  rw [ExactHodgeCertificate.adjoint_mul]
  have hunit := adjoint_edgeTranslationUnit_mul_self T j k
  rw [show
      (adjoint
          (cornerBoundaryCoefficient T j k i +
            cornerBoundaryCoefficient T j (nextCorner k) i) *
          adjoint (edgeTranslationUnit T j k)) *
          (edgeTranslationUnit T j k *
            (cornerBoundaryCoefficient T j k l +
              cornerBoundaryCoefficient T j (nextCorner k) l)) =
        adjoint
          (cornerBoundaryCoefficient T j k i +
            cornerBoundaryCoefficient T j (nextCorner k) i) *
          ((adjoint (edgeTranslationUnit T j k) *
              edgeTranslationUnit T j k) *
            (cornerBoundaryCoefficient T j k l +
              cornerBoundaryCoefficient T j (nextCorner k) l)) by
        simp only [mul_assoc]]
  rw [hunit]
  simp

/-- Sum of the three local edge energies.  Pure three-cycle algebra turns it
into the Fox-row Gram term plus one diagonal term for each literal
occurrence. -/
theorem sum_adjoint_edgeDifference_mul_edgeDifference
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (i l : Generator) :
    (∑ k : Fin 3,
      adjoint (edgeDifference T j k i) * edgeDifference T j k l) =
      adjoint (boundary T j i) * boundary T j l +
        ∑ k : Fin 3,
          adjoint (cornerBoundaryCoefficient T j k i) *
            cornerBoundaryCoefficient T j k l := by
  simp_rw [adjoint_edgeDifference_mul_edgeDifference,
    boundary_eq_sum_cornerBoundaryCoefficient]
  simp [Fin.sum_univ_succ, nextCorner, adjoint_add]
  noncomm_ring

/-- A single Fox corner is a signed group-ring unit in exactly one generator
coordinate, so its diagonal Gram term is a literal occurrence indicator. -/
theorem adjoint_cornerBoundaryCoefficient_mul
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) (i l : Generator) :
    adjoint (cornerBoundaryCoefficient T j k i) *
        cornerBoundaryCoefficient T j k l =
      if i = (T j k).1 ∧ l = (T j k).1 then 1 else 0 := by
  rcases h : T j k with ⟨g, s⟩
  cases s <;> by_cases hi : i = g <;> by_cases hl : l = g <;>
    simp [cornerBoundaryCoefficient, cornerValue, h, hi, hl, mul_assoc,
      MonoidAlgebra.one_def]

/-- Pullback of the exact rational link Laplacian along the signed-coordinate
matrix. -/
noncomputable def linkLaplacianPullback
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i l : Generator) : RatGroupRing (Presented T) :=
  ∑ u, ∑ v,
    adjoint (orientedCoefficient T u i) *
      MonoidAlgebra.single 1 (rationalLinkLaplacian T u v) *
        orientedCoefficient T v l

theorem directedAdjacencyCount_eq_sum
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u v : SignedGenerator (Generator := Generator)) :
    directedAdjacencyCount T u v =
      ∑ j, ∑ k : Fin 3,
        if T j k = u ∧ inverseSigned (T j (nextCorner k)) = v
        then 1 else 0 := by
  classical
  unfold directedAdjacencyCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]

/-- Embed a finite natural indicator count as a scalar group-ring sum. -/
theorem single_cast_indicator_sum {E : Type*} [Fintype E]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (p : E → Prop) [DecidablePred p] :
    (MonoidAlgebra.single 1 ((↑(∑ e, if p e then 1 else 0) : ℚ)) :
      RatGroupRing (Presented T)) =
      ∑ e, if p e then 1 else 0 := by
  classical
  have hcast :
      ((↑(∑ e, if p e then 1 else 0) : ℚ)) =
        ∑ e, if p e then (1 : ℚ) else 0 := by
    rfl
  rw [hcast]
  calc
    (MonoidAlgebra.single 1
        (∑ e, if p e then (1 : ℚ) else 0) :
      RatGroupRing (Presented T)) =
        ∑ e, MonoidAlgebra.single 1
          (if p e then (1 : ℚ) else 0) := by
            exact map_sum
              (MonoidAlgebra.singleAddHom (R := ℚ) (M := Presented T) 1)
              (fun e ↦ if p e then (1 : ℚ) else 0) Finset.univ
    _ = ∑ e, if p e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hp : p e
      · simp only [hp, if_true]
        exact MonoidAlgebra.one_def.symm
      · simp only [hp, if_false]
        exact MonoidAlgebra.single_zero (1 : Presented T)

/-- Two nested finite indicator sums, flattened only at the scalar embedding
boundary. -/
theorem single_cast_nested_indicator_sum
    {E F : Type*} [Fintype E] [Fintype F]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (p : E → F → Prop) [∀ e f, Decidable (p e f)] :
    (MonoidAlgebra.single 1
        ((↑(∑ e, ∑ f, if p e f then 1 else 0) : ℚ)) :
      RatGroupRing (Presented T)) =
      ∑ ef : E × F, if p ef.1 ef.2 then 1 else 0 := by
  classical
  calc
    (MonoidAlgebra.single 1
        ((↑(∑ e, ∑ f, if p e f then 1 else 0) : ℚ)) :
      RatGroupRing (Presented T)) =
        MonoidAlgebra.single 1
          ((↑(∑ ef : E × F, if p ef.1 ef.2 then 1 else 0) : ℚ)) := by
            congr 2
            exact (Fintype.sum_prod_type
              (f := fun ef : E × F ↦ if p ef.1 ef.2 then 1 else 0)).symm
    _ = _ := single_cast_indicator_sum T
      (fun ef : E × F ↦ p ef.1 ef.2)

theorem incidence_sum_rotate {A B C M : Type*}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M]
    (f : A → B → C → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem sum_single_indicator {S R : Type*}
    [Fintype S] [DecidableEq S] [Semiring R]
    (a b : S → R) (x : S) :
    (∑ u, a u * (if x = u then 1 else 0) * b u) = a x * b x := by
  have hterm (u : S) :
      a u * (if x = u then 1 else 0) * b u =
        if u = x then a u * b u else 0 := by
    by_cases hu : u = x
    · subst u
      simp
    · have hxu : x ≠ u := fun h ↦ hu h.symm
      simp [hu, hxu]
  simp_rw [hterm]
  rw [Fintype.sum_ite_eq']

theorem sum_double_indicator {S R : Type*}
    [Fintype S] [DecidableEq S] [Semiring R]
    (a b : S → R) (x y : S) :
    (∑ u, ∑ v, a u * (if x = u ∧ y = v then 1 else 0) * b v) =
      a x * b y := by
  have hterm (u v : S) :
      a u * (if x = u ∧ y = v then 1 else 0) * b v =
        if v = y then if u = x then a u * b v else 0 else 0 := by
    by_cases hu : u = x <;> by_cases hv : v = y
    · subst u
      subst v
      simp
    · have hy : y ≠ v := fun h ↦ hv h.symm
      simp [hu, hv, hy]
    · have hx : x ≠ u := fun h ↦ hu h.symm
      simp [hu, hx]
    · have hx : x ≠ u := fun h ↦ hu h.symm
      simp [hu, hx]
  simp_rw [hterm]
  have hinner (u : S) :
      (∑ v, if v = y then if u = x then a u * b v else 0 else 0) =
        if u = x then a u * b y else 0 := by
    rw [Fintype.sum_ite_eq']
  simp_rw [hinner]
  rw [Fintype.sum_ite_eq']

/-- The source-diagonal part of incidence energy. -/
theorem sourceDiagonal_incidence_core
    (T : TriangleIndex → Triangle (Generator := Generator)) (i l : Generator) :
    (∑ u,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1
          ((↑(∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0) : ℚ)) *
        orientedCoefficient T u l) =
      ∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T (T j k) i) *
          orientedCoefficient T (T j k) l := by
  classical
  simp_rw [single_cast_nested_indicator_sum T]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hrhs :
      (∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T (T j k) i) *
          orientedCoefficient T (T j k) l) =
      ∑ e : TriangleIndex × Fin 3,
        adjoint (orientedCoefficient T (T e.1 e.2) i) *
          orientedCoefficient T (T e.1 e.2) l :=
    (Fintype.sum_prod_type (f := fun e : TriangleIndex × Fin 3 ↦
      adjoint (orientedCoefficient T (T e.1 e.2) i) *
        orientedCoefficient T (T e.1 e.2) l)).symm
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro e he
  exact sum_single_indicator
    (fun u ↦ adjoint (orientedCoefficient T u i))
    (fun u ↦ orientedCoefficient T u l) (T e.1 e.2)

/-- The target-diagonal part of incidence energy. -/
theorem targetDiagonal_incidence_core
    (T : TriangleIndex → Triangle (Generator := Generator)) (i l : Generator) :
    (∑ u,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1
          ((↑(∑ j, ∑ k : Fin 3,
            if inverseSigned (T j (nextCorner k)) = u then 1 else 0) : ℚ)) *
        orientedCoefficient T u l) =
      ∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T
            (inverseSigned (T j (nextCorner k))) i) *
          orientedCoefficient T
            (inverseSigned (T j (nextCorner k))) l := by
  classical
  simp_rw [single_cast_nested_indicator_sum T]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hrhs :
      (∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T
            (inverseSigned (T j (nextCorner k))) i) *
          orientedCoefficient T
            (inverseSigned (T j (nextCorner k))) l) =
      ∑ e : TriangleIndex × Fin 3,
        adjoint (orientedCoefficient T
            (inverseSigned (T e.1 (nextCorner e.2))) i) *
          orientedCoefficient T
            (inverseSigned (T e.1 (nextCorner e.2))) l :=
    (Fintype.sum_prod_type (f := fun e : TriangleIndex × Fin 3 ↦
      adjoint (orientedCoefficient T
          (inverseSigned (T e.1 (nextCorner e.2))) i) *
        orientedCoefficient T
          (inverseSigned (T e.1 (nextCorner e.2))) l)).symm
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro e he
  exact sum_single_indicator
    (fun u ↦ adjoint (orientedCoefficient T u i))
    (fun u ↦ orientedCoefficient T u l)
    (inverseSigned (T e.1 (nextCorner e.2)))

/-- The source-incidence count embedded on the diagonal of signed-link
coordinates. -/
theorem sourceDiagonal_incidence
    (T : TriangleIndex → Triangle (Generator := Generator)) (i l : Generator) :
    (∑ u, ∑ v,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1
          (if u = v then
            (↑(∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0) : ℚ)
          else 0) *
        orientedCoefficient T v l) =
      ∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T (T j k) i) *
          orientedCoefficient T (T j k) l := by
  classical
  have hrow (u : SignedGenerator (Generator := Generator)) :
      (∑ v,
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1
            (if u = v then
              (↑(∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0) : ℚ)
            else 0) *
          orientedCoefficient T v l) =
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1
            ((↑(∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0) : ℚ)) *
          orientedCoefficient T u l := by
    have hterm (v : SignedGenerator (Generator := Generator)) :
        adjoint (orientedCoefficient T u i) *
            MonoidAlgebra.single 1
              (if u = v then
                (↑(∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0) : ℚ)
              else 0) *
            orientedCoefficient T v l =
          if v = u then
            adjoint (orientedCoefficient T u i) *
              MonoidAlgebra.single 1
                ((↑(∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0) : ℚ)) *
              orientedCoefficient T v l
          else 0 := by
      by_cases hv : v = u
      · subst v
        simp only [if_pos]
      · have huv : u ≠ v := fun h ↦ hv h.symm
        simp only [hv, huv, if_false]
        rw [MonoidAlgebra.single_zero, mul_zero, zero_mul]
    simp_rw [hterm]
    rw [Fintype.sum_ite_eq']
  simp_rw [hrow]
  exact sourceDiagonal_incidence_core T i l

/-- The target-incidence count embedded on the diagonal of signed-link
coordinates. -/
theorem targetDiagonal_incidence
    (T : TriangleIndex → Triangle (Generator := Generator)) (i l : Generator) :
    (∑ u, ∑ v,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1
          (if u = v then
            (↑(∑ j, ∑ k : Fin 3,
              if inverseSigned (T j (nextCorner k)) = u then 1 else 0) : ℚ)
          else 0) *
        orientedCoefficient T v l) =
      ∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T
            (inverseSigned (T j (nextCorner k))) i) *
          orientedCoefficient T
            (inverseSigned (T j (nextCorner k))) l := by
  classical
  have hrow (u : SignedGenerator (Generator := Generator)) :
      (∑ v,
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1
            (if u = v then
              (↑(∑ j, ∑ k : Fin 3,
                if inverseSigned (T j (nextCorner k)) = u then 1 else 0) : ℚ)
            else 0) *
          orientedCoefficient T v l) =
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1
            ((↑(∑ j, ∑ k : Fin 3,
              if inverseSigned (T j (nextCorner k)) = u then 1 else 0) : ℚ)) *
          orientedCoefficient T u l := by
    have hterm (v : SignedGenerator (Generator := Generator)) :
        adjoint (orientedCoefficient T u i) *
            MonoidAlgebra.single 1
              (if u = v then
                (↑(∑ j, ∑ k : Fin 3,
                  if inverseSigned (T j (nextCorner k)) = u then 1 else 0) : ℚ)
              else 0) *
            orientedCoefficient T v l =
          if v = u then
            adjoint (orientedCoefficient T u i) *
              MonoidAlgebra.single 1
                ((↑(∑ j, ∑ k : Fin 3,
                  if inverseSigned (T j (nextCorner k)) = u then 1 else 0) : ℚ)) *
              orientedCoefficient T v l
          else 0 := by
      by_cases hv : v = u
      · subst v
        simp only [if_pos]
      · have huv : u ≠ v := fun h ↦ hv h.symm
        simp only [hv, huv, if_false]
        rw [MonoidAlgebra.single_zero, mul_zero, zero_mul]
    simp_rw [hterm]
    rw [Fintype.sum_ite_eq']
  simp_rw [hrow]
  exact targetDiagonal_incidence_core T i l

theorem directed_incidence_core
    (T : TriangleIndex → Triangle (Generator := Generator))
    (s t : TriangleIndex → Fin 3 →
      SignedGenerator (Generator := Generator)) (i l : Generator) :
    (∑ u, ∑ v,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1
          ((↑(∑ j, ∑ k : Fin 3,
            if s j k = u ∧ t j k = v
            then 1 else 0) : ℚ)) *
        orientedCoefficient T v l) =
      ∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T (s j k) i) *
          orientedCoefficient T (t j k) l := by
  classical
  simp_rw [single_cast_nested_indicator_sum T]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [incidence_sum_rotate]
  have hrhs :
      (∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T (s j k) i) *
          orientedCoefficient T (t j k) l) =
      ∑ e : TriangleIndex × Fin 3,
        adjoint (orientedCoefficient T (s e.1 e.2) i) *
          orientedCoefficient T (t e.1 e.2) l :=
    (Fintype.sum_prod_type (f := fun e : TriangleIndex × Fin 3 ↦
      adjoint (orientedCoefficient T (s e.1 e.2) i) *
        orientedCoefficient T (t e.1 e.2) l)).symm
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro e he
  exact sum_double_indicator
    (fun u ↦ adjoint (orientedCoefficient T u i))
    (fun v ↦ orientedCoefficient T v l)
    (s e.1 e.2) (t e.1 e.2)

/-- The forward directed cross-energy. -/
theorem forward_incidence
    (T : TriangleIndex → Triangle (Generator := Generator)) (i l : Generator) :
    (∑ u, ∑ v,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1
          ((↑(∑ j, ∑ k : Fin 3,
            if T j k = u ∧ inverseSigned (T j (nextCorner k)) = v
            then 1 else 0) : ℚ)) *
        orientedCoefficient T v l) =
      ∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T (T j k) i) *
          orientedCoefficient T (inverseSigned (T j (nextCorner k))) l :=
  directed_incidence_core T (fun j k ↦ T j k)
    (fun j k ↦ inverseSigned (T j (nextCorner k))) i l

/-- The reverse directed cross-energy. -/
theorem reverse_incidence
    (T : TriangleIndex → Triangle (Generator := Generator)) (i l : Generator) :
    (∑ u, ∑ v,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1
          ((↑(∑ j, ∑ k : Fin 3,
            if T j k = v ∧ inverseSigned (T j (nextCorner k)) = u
            then 1 else 0) : ℚ)) *
        orientedCoefficient T v l) =
      ∑ j, ∑ k : Fin 3,
        adjoint (orientedCoefficient T
            (inverseSigned (T j (nextCorner k))) i) *
          orientedCoefficient T (T j k) l := by
  classical
  simpa only [and_comm] using
    (directed_incidence_core T
      (fun j k ↦ inverseSigned (T j (nextCorner k)))
      (fun j k ↦ T j k) i l)

/-- Number of literal occurrences of an underlying generator. -/
def generatorOccurrenceCount
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i : Generator) : ℕ :=
  ((Finset.univ : Finset (TriangleIndex × Fin 3)).filter fun p ↦
    (T p.1 p.2).1 = i).card

theorem generatorOccurrenceCount_eq_sum
    (T : TriangleIndex → Triangle (Generator := Generator)) (i : Generator) :
    generatorOccurrenceCount T i =
      ∑ j, ∑ k : Fin 3, if (T j k).1 = i then 1 else 0 := by
  classical
  unfold generatorOccurrenceCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]

/-- Expand a signed vertex degree as its outgoing occurrences plus the
incoming occurrences at cyclic successors.  Keeping this bookkeeping lemma
separate prevents the later three-corner argument from expanding nested
finite filters repeatedly. -/
theorem degree_eq_sum_signed_occurrences
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u : SignedGenerator (Generator := Generator)) :
    degree T u =
      ∑ j, ∑ k : Fin 3,
        ((if T j k = u then 1 else 0) +
          if inverseSigned (T j (nextCorner k)) = u then 1 else 0) := by
  classical
  have hout :
      (∑ v, directedAdjacencyCount T u v) =
        ∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0 := by
    unfold directedAdjacencyCount
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : T j k = u <;> simp [h]
  have hin :
      (∑ v, directedAdjacencyCount T v u) =
        ∑ j, ∑ k : Fin 3,
          if inverseSigned (T j (nextCorner k)) = u then 1 else 0 := by
    unfold directedAdjacencyCount
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : inverseSigned (T j (nextCorner k)) = u <;> simp [h]
  unfold degree adjacencyCount
  rw [Finset.sum_add_distrib, hout, hin]
  simp_rw [Finset.sum_add_distrib]

/-- Cyclic successor merely permutes a sum over the three corners. -/
theorem sum_nextCorner (f : Fin 3 → ℕ) :
    (∑ k : Fin 3, f (nextCorner k)) = ∑ k : Fin 3, f k := by
  simp [Fin.sum_univ_succ, nextCorner, add_assoc, add_left_comm, add_comm]

/-- The two possible incidences at one signed literal partition the
underlying-generator occurrence. -/
theorem signed_occurrence_partition
    (u : SignedGenerator (Generator := Generator))
    (i : Generator) (sign : Bool) :
    (if u = (i, sign) then 1 else 0) +
        (if inverseSigned u = (i, sign) then 1 else 0) =
      if u.1 = i then 1 else 0 := by
  rcases u with ⟨g, s⟩
  cases s <;> cases sign <;> by_cases h : g = i <;>
    simp [inverseSigned, h]

/-- On one cyclic triangle, the two signed incidence counts above a fixed
underlying generator forget the sign and count exactly its literals. -/
theorem sum_signed_occurrences_triangle
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (i : Generator) (sign : Bool) :
    (∑ k : Fin 3,
      ((if T j k = (i, sign) then 1 else 0) +
        if inverseSigned (T j (nextCorner k)) = (i, sign) then 1 else 0)) =
      ∑ k : Fin 3, if (T j k).1 = i then 1 else 0 := by
  rw [Finset.sum_add_distrib]
  rw [sum_nextCorner (fun k ↦
    if inverseSigned (T j k) = (i, sign) then 1 else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact signed_occurrence_partition (T j k) i sign

/-- The degree of either signed vertex is the total number of occurrences of
its underlying generator.  Cyclic successor is a permutation of the three
corners, so incoming and outgoing directed counts partition the two signs. -/
theorem degree_eq_generatorOccurrenceCount
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i : Generator) (sign : Bool) :
    degree T (i, sign) = generatorOccurrenceCount T i := by
  classical
  rw [degree_eq_sum_signed_occurrences, generatorOccurrenceCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact sum_signed_occurrences_triangle T j i sign

/-- Pointwise decomposition of the rational link Laplacian into the two
diagonal incidence counts and the two directed edge counts. -/
theorem rationalLinkLaplacian_eq_incidence_components
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u v : SignedGenerator (Generator := Generator)) :
    rationalLinkLaplacian T u v =
      (if u = v then
        (↑(∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0) : ℚ)
      else 0) +
      (if u = v then
        (↑(∑ j, ∑ k : Fin 3,
          if inverseSigned (T j (nextCorner k)) = u then 1 else 0) : ℚ)
      else 0) -
      (↑(∑ j, ∑ k : Fin 3,
        if T j k = u ∧ inverseSigned (T j (nextCorner k)) = v
        then 1 else 0) : ℚ) -
      (↑(∑ j, ∑ k : Fin 3,
        if T j k = v ∧ inverseSigned (T j (nextCorner k)) = u
        then 1 else 0) : ℚ) := by
  classical
  unfold rationalLinkLaplacian linkLaplacian adjacencyCount
  rw [degree_eq_sum_signed_occurrences]
  simp_rw [directedAdjacencyCount_eq_sum]
  push_cast
  by_cases huv : u = v
  · simp only [huv, if_true, Finset.sum_add_distrib]
    ring
  · simp only [huv, if_false, Finset.sum_add_distrib]
    ring

/-- Pulling back the pointwise incidence decomposition commutes with the two
finite coordinate sums.  This deliberately isolates distributivity from the
four combinatorial incidence lemmas. -/
theorem linkLaplacianPullback_eq_incidenceEnergy
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i l : Generator) :
    linkLaplacianPullback T i l =
      (∑ u, ∑ v,
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1
            (if u = v then
              (↑(∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0) : ℚ)
            else 0) *
          orientedCoefficient T v l) +
      (∑ u, ∑ v,
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1
            (if u = v then
              (↑(∑ j, ∑ k : Fin 3,
                if inverseSigned (T j (nextCorner k)) = u then 1 else 0) : ℚ)
            else 0) *
          orientedCoefficient T v l) -
      (∑ u, ∑ v,
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1
            ((↑(∑ j, ∑ k : Fin 3,
              if T j k = u ∧ inverseSigned (T j (nextCorner k)) = v
              then 1 else 0) : ℚ)) *
          orientedCoefficient T v l) -
      (∑ u, ∑ v,
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1
            ((↑(∑ j, ∑ k : Fin 3,
              if T j k = v ∧ inverseSigned (T j (nextCorner k)) = u
              then 1 else 0) : ℚ)) *
          orientedCoefficient T v l) := by
  classical
  unfold linkLaplacianPullback
  calc
    _ = ∑ u, ∑ v,
        (adjoint (orientedCoefficient T u i) *
            MonoidAlgebra.single 1
              (if u = v then
                (↑(∑ j, ∑ k : Fin 3, if T j k = u then 1 else 0) : ℚ)
              else 0) * orientedCoefficient T v l +
          adjoint (orientedCoefficient T u i) *
            MonoidAlgebra.single 1
              (if u = v then
                (↑(∑ j, ∑ k : Fin 3,
                  if inverseSigned (T j (nextCorner k)) = u then 1 else 0) : ℚ)
              else 0) * orientedCoefficient T v l -
          adjoint (orientedCoefficient T u i) *
            MonoidAlgebra.single 1
              ((↑(∑ j, ∑ k : Fin 3,
                if T j k = u ∧ inverseSigned (T j (nextCorner k)) = v
                then 1 else 0) : ℚ)) * orientedCoefficient T v l -
          adjoint (orientedCoefficient T u i) *
            MonoidAlgebra.single 1
              ((↑(∑ j, ∑ k : Fin 3,
                if T j k = v ∧ inverseSigned (T j (nextCorner k)) = u
                then 1 else 0) : ℚ)) * orientedCoefficient T v l) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [rationalLinkLaplacian_eq_incidence_components]
      simp only [MonoidAlgebra.single_add, MonoidAlgebra.single_sub,
        mul_add, mul_sub, add_mul, sub_mul]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum_four_components {A B M : Type*}
    [Fintype A] [Fintype B] [AddCommGroup M]
    (a b c d : A → B → M) :
    (∑ x, ∑ y, a x y) + (∑ x, ∑ y, b x y) -
        (∑ x, ∑ y, c x y) - (∑ x, ∑ y, d x y) =
      ∑ x, ∑ y, (a x y + b x y - c x y - d x y) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Incidence-matrix identity for the corrected link multigraph. -/
theorem linkLaplacianPullback_eq_sum_edgeDifference
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i l : Generator) :
    linkLaplacianPullback T i l =
      ∑ j, ∑ k : Fin 3,
        adjoint (edgeDifference T j k i) * edgeDifference T j k l := by
  classical
  rw [linkLaplacianPullback_eq_incidenceEnergy]
  rw [sourceDiagonal_incidence, targetDiagonal_incidence,
    forward_incidence, reverse_incidence]
  rw [sum_four_components]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [edgeDifference, ExactHodgeCertificate.adjoint_sub]
  noncomm_ring

/-- The literal Fox diagonal terms count generator occurrences. -/
theorem sum_adjoint_cornerBoundaryCoefficient_mul
    (T : TriangleIndex → Triangle (Generator := Generator)) (i l : Generator) :
    (∑ j, ∑ k : Fin 3,
      adjoint (cornerBoundaryCoefficient T j k i) *
        cornerBoundaryCoefficient T j k l) =
      if i = l then
        MonoidAlgebra.single 1 (generatorOccurrenceCount T i : ℚ)
      else 0 := by
  classical
  simp_rw [adjoint_cornerBoundaryCoefficient_mul]
  by_cases h : i = l
  · subst l
    rw [if_pos rfl, generatorOccurrenceCount_eq_sum]
    simp only [and_self]
    have hcount :
        (∑ j, ∑ k : Fin 3, if i = (T j k).1 then 1 else 0) =
          ∑ j, ∑ k : Fin 3, if (T j k).1 = i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hik : i = (T j k).1
      · rw [if_pos hik, if_pos hik.symm]
      · have hki : (T j k).1 ≠ i := fun hki ↦ hik hki.symm
        rw [if_neg hik, if_neg hki]
    have hsingle :
        (∑ j, ∑ k : Fin 3,
          if i = (T j k).1 then (1 : RatGroupRing (Presented T)) else 0) =
          MonoidAlgebra.single 1
            ((↑(∑ j, ∑ k : Fin 3,
              if i = (T j k).1 then 1 else 0) : ℚ)) := by
      let e (j : TriangleIndex) (k : Fin 3) : ℚ :=
        if i = (T j k).1 then 1 else 0
      have hpoint (j : TriangleIndex) (k : Fin 3) :
          (if i = (T j k).1 then
              (1 : RatGroupRing (Presented T)) else 0) =
            MonoidAlgebra.singleAddHom 1 (e j k) := by
        by_cases hik : i = (T j k).1 <;>
          simp [e, hik, MonoidAlgebra.one_def]
      calc
        (∑ j, ∑ k : Fin 3,
          if i = (T j k).1 then
            (1 : RatGroupRing (Presented T)) else 0) =
          ∑ j, ∑ k : Fin 3,
            MonoidAlgebra.singleAddHom 1 (e j k) := by
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              exact hpoint j k
        _ = MonoidAlgebra.singleAddHom 1 (∑ j, ∑ k : Fin 3, e j k) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [map_sum]
        _ = _ := by
              congr 1
    calc
      _ = MonoidAlgebra.single 1
          ((↑(∑ j, ∑ k : Fin 3,
            if i = (T j k).1 then 1 else 0) : ℚ)) := hsingle
      _ = _ := by
        congr 1
        exact_mod_cast hcount
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg]
    rintro ⟨hi, hl⟩
    exact h (hi.trans hl.symm)

/-- **Exact global Fox/link identity.**  For a regular triangular link, the
pullback of its integral Laplacian is `B⁺B + dI`. -/
theorem linkLaplacianPullback_eq_boundaryGram_add_diagonal
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (hregular : ∀ u, degree T u = regularDegree)
    (i l : Generator) :
    linkLaplacianPullback T i l =
      (∑ j, adjoint (boundary T j i) * boundary T j l) +
        if i = l then MonoidAlgebra.single 1 (regularDegree : ℚ) else 0 := by
  rw [linkLaplacianPullback_eq_sum_edgeDifference]
  simp_rw [sum_adjoint_edgeDifference_mul_edgeDifference,
    Finset.sum_add_distrib]
  rw [sum_adjoint_cornerBoundaryCoefficient_mul]
  have hcount : generatorOccurrenceCount T i = regularDegree := by
    rw [← degree_eq_generatorOccurrenceCount T i false]
    exact hregular (i, false)
  rw [hcount]

/-! ## Exact rational spectral-certificate tables -/

section SpectralCertificate

variable [Nonempty Generator]

/-- Every nonnegative rational scalar has a four-row rational Gram factor.
This is the rational form of Lagrange's four-square theorem and removes all
square-root choices from the certificate assembly. -/
theorem exists_four_square_factor (x : ℚ) (hx : 0 ≤ x) :
    ∃ a : Fin 4 → ℚ, ∑ k, a k ^ 2 = x := by
  have hnum : 0 ≤ x.num := Rat.num_nonneg.mpr hx
  obtain ⟨a, b, c, d, hs⟩ :=
    Nat.sum_four_squares (x.num.natAbs * x.den)
  let q : Fin 4 → ℚ :=
    ![(a : ℚ) / x.den, (b : ℚ) / x.den,
      (c : ℚ) / x.den, (d : ℚ) / x.den]
  refine ⟨q, ?_⟩
  rw [← x.num_div_den]
  have hnumAbs : (x.num.natAbs : ℤ) = x.num :=
    Int.natAbs_of_nonneg hnum
  have hsQ :
      (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 + (d : ℚ) ^ 2 =
        (x.num : ℚ) * x.den := by
    rw [← hnumAbs]
    exact_mod_cast hs
  simp [q, Fin.sum_univ_succ]
  field_simp [Rat.den_nz]
  nlinarith

/-- Orthogonal projector onto the mean-zero coordinate subspace, as an exact
rational matrix. -/
def meanZeroProjector
    (u v : SignedGenerator (Generator := Generator)) : ℚ :=
  (if u = v then 1 else 0) -
    1 / Fintype.card (SignedGenerator (Generator := Generator))

/-- Rational Gram matrix of a finite row family. -/
def gramMatrix {Row : Type} [Fintype Row]
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (u v : SignedGenerator (Generator := Generator)) : ℚ :=
  ∑ row, q row u * q row v

/-- Pointwise residual for the exact normalized-link identity
`L/d = gap · P₀ + QᵀQ`.  A concrete finite table discharges its vanishing by
`decide` or rational normalization. -/
def linkGapResidual {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (u v : SignedGenerator (Generator := Generator)) : ℚ :=
  rationalLinkLaplacian T u v / regularDegree -
    gap * meanZeroProjector u v - gramMatrix q u v

/-- The finite, decidable checks expected from a concrete triangular link
certificate.  This is a predicate on explicit tables, not an existence or
literature premise. -/
def LinkCertificateChecks {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ) : Prop :=
  0 < regularDegree ∧
    (1 : ℚ) / 2 < gap ∧
    (∀ u, degree T u = regularDegree) ∧
    ∀ u v, linkGapResidual T regularDegree gap q u v = 0

noncomputable instance instDecidableLinkCertificateChecks {Row : Type}
    [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ) :
    Decidable (LinkCertificateChecks T regularDegree gap q) := by
  classical
  infer_instance

theorem linkGap_identity_of_checks {Row : Type} [Fintype Row]
    {T : TriangleIndex → Triangle (Generator := Generator)}
    {regularDegree : ℕ} {gap : ℚ}
    {q : Row → SignedGenerator (Generator := Generator) → ℚ}
    (h : LinkCertificateChecks T regularDegree gap q)
    (u v : SignedGenerator (Generator := Generator)) :
    rationalLinkLaplacian T u v / regularDegree =
      gap * meanZeroProjector u v + gramMatrix q u v := by
  have hz := h.2.2.2 u v
  unfold linkGapResidual at hz
  linarith

theorem linkGap_gt_half_of_checks {Row : Type} [Fintype Row]
    {T : TriangleIndex → Triangle (Generator := Generator)}
    {regularDegree : ℕ} {gap : ℚ}
    {q : Row → SignedGenerator (Generator := Generator) → ℚ}
    (h : LinkCertificateChecks T regularDegree gap q) :
    (1 : ℚ) / 2 < gap := h.2.1

/-! ## Rational group-ring Garland certificate -/

/-- Fox row divided by the positive regular degree. -/
noncomputable def scaledBoundary
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (j : TriangleIndex) (i : Generator) :
    RatGroupRing (Presented T) :=
  MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree) * boundary T j i

/-- Pull one rational link-Gram row back to generator coordinates. -/
noncomputable def unscaledLinkRow {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (row : Row) (i : Generator) : RatGroupRing (Presented T) :=
  ∑ u, MonoidAlgebra.single 1 (q row u) *
    orientedCoefficient T u i

/-- Pull one rational link-Gram row back to generator coordinates, scaled by
`1/d`.  Taking `d` identical copies produces the required coefficient `1/d`
without a square root. -/
noncomputable def liftedLinkRow {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (row : Row) (i : Generator) : RatGroupRing (Presented T) :=
  MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree) *
    unscaledLinkRow T q row i

/-- The scalar left after pulling back the mean-zero projector. -/
def garlandCoboundaryCoefficient
    (regularDegree : ℕ) (gap : ℚ) : ℚ :=
  1 - gap /
    (Fintype.card (SignedGenerator (Generator := Generator)) * regularDegree)

/-- The remaining scalar is nonnegative.  The diagonal of the normalized
link identity bounds `gap ≤ 2`; meanwhile a nonempty generator alphabet and
positive degree give at least two signed edge ends. -/
theorem garlandCoboundaryCoefficient_nonneg {Row : Type} [Fintype Row]
    {T : TriangleIndex → Triangle (Generator := Generator)}
    {regularDegree : ℕ} {gap : ℚ}
    {q : Row → SignedGenerator (Generator := Generator) → ℚ}
    (h : LinkCertificateChecks T regularDegree gap q) :
    0 ≤ garlandCoboundaryCoefficient
      (Generator := Generator) regularDegree gap := by
  let u : SignedGenerator (Generator := Generator) :=
    (Classical.choice inferInstance, false)
  let n := Fintype.card (SignedGenerator (Generator := Generator))
  have hd : (0 : ℚ) < regularDegree := by exact_mod_cast h.1
  have hnNat : 2 ≤ n := by
    have hGenerator : 0 < Fintype.card Generator := Fintype.card_pos
    have hcard := Nat.mul_le_mul_right 2 (Nat.succ_le_iff.mpr hGenerator)
    simpa [n, Fintype.card_prod] using hcard
  have hn : (2 : ℚ) ≤ n := by exact_mod_cast hnNat
  have hP : (1 : ℚ) / 2 ≤ meanZeroProjector u u := by
    unfold meanZeroProjector
    rw [if_pos rfl]
    have hnpos : (0 : ℚ) < n :=
      lt_of_lt_of_le (by norm_num : (0 : ℚ) < 2) hn
    have hinv := (div_le_div_iff_of_pos_left (by norm_num : (0 : ℚ) < 1)
      hnpos (by norm_num : (0 : ℚ) < 2)).2 hn
    linarith
  have hGram : 0 ≤ gramMatrix q u u := by
    unfold gramMatrix
    exact Finset.sum_nonneg fun row _ ↦ mul_self_nonneg (q row u)
  have hLle : rationalLinkLaplacian T u u / regularDegree ≤ 1 := by
    unfold rationalLinkLaplacian linkLaplacian
    simp only [if_pos]
    rw [h.2.2.1 u]
    have ha : (0 : ℚ) ≤ (adjacencyCount T u u : ℚ) := by
      exact_mod_cast Nat.zero_le (adjacencyCount T u u)
    push_cast
    exact (div_le_iff₀ hd).2 (by linarith)
  have hid := linkGap_identity_of_checks h u u
  have hgap0 : 0 < gap := lt_trans (by norm_num) h.2.1
  have hgap_le_two : gap ≤ 2 := by
    have : gap * ((1 : ℚ) / 2) ≤ 1 := by
      calc
        gap * ((1 : ℚ) / 2) ≤ gap * meanZeroProjector u u :=
          mul_le_mul_of_nonneg_left hP hgap0.le
        _ ≤ rationalLinkLaplacian T u u / regularDegree := by
          rw [hid]
          exact le_add_of_nonneg_right hGram
        _ ≤ 1 := hLle
    linarith
  have hnd : (2 : ℚ) ≤ n * regularDegree := by
    have hd1 : (1 : ℚ) ≤ regularDegree := by exact_mod_cast h.1
    nlinarith
  unfold garlandCoboundaryCoefficient
  have hden : (0 : ℚ) < n * regularDegree := lt_of_lt_of_le (by norm_num) hnd
  apply sub_nonneg.mpr
  exact (div_le_one hden).2 (hgap_le_two.trans hnd)

/-- Canonical four-square factor for the nonnegative coboundary coefficient. -/
noncomputable def coboundaryFactor {Row : Type} [Fintype Row]
    {T : TriangleIndex → Triangle (Generator := Generator)}
    {regularDegree : ℕ} {gap : ℚ}
    {q : Row → SignedGenerator (Generator := Generator) → ℚ}
    (h : LinkCertificateChecks T regularDegree gap q) : Fin 4 → ℚ :=
  Classical.choose (exists_four_square_factor
    (garlandCoboundaryCoefficient (Generator := Generator) regularDegree gap)
    (garlandCoboundaryCoefficient_nonneg h))

theorem sum_sq_coboundaryFactor {Row : Type} [Fintype Row]
    {T : TriangleIndex → Triangle (Generator := Generator)}
    {regularDegree : ℕ} {gap : ℚ}
    {q : Row → SignedGenerator (Generator := Generator) → ℚ}
    (h : LinkCertificateChecks T regularDegree gap q) :
    ∑ k, coboundaryFactor h k ^ 2 =
      garlandCoboundaryCoefficient
        (Generator := Generator) regularDegree gap :=
  Classical.choose_spec (exists_four_square_factor
    (garlandCoboundaryCoefficient (Generator := Generator) regularDegree gap)
    (garlandCoboundaryCoefficient_nonneg h))

/-- Row type of the assembled group-ring Gram factor. -/
abbrev GarlandRow (regularDegree : ℕ) (Row : Type) :=
  (Fin regularDegree × Row) ⊕ Fin 4

/-- Complete rational group-ring Gram factor: duplicated pulled-back link rows
on the left, and four coboundary rows on the right. -/
noncomputable def garlandGramRow {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (h : LinkCertificateChecks T regularDegree gap q) :
    GarlandRow regularDegree Row → Generator → RatGroupRing (Presented T)
  | Sum.inl copyRow, i =>
      liftedLinkRow T regularDegree q copyRow.2 i
  | Sum.inr k, i =>
      MonoidAlgebra.single 1 (coboundaryFactor h k) *
        adjoint (generatorCoboundary (generator T) i)

/-- Positive scalar furnished by the strict one-half link gap. -/
def garlandGap (regularDegree : ℕ) (gap : ℚ) : ℚ :=
  (2 * gap - 1) / regularDegree

/-- Gram matrix obtained by pulling back the finite rational link factor. -/
noncomputable def linkGramPullback {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (i l : Generator) : RatGroupRing (Presented T) :=
  ∑ u, ∑ v,
    adjoint (orientedCoefficient T u i) *
      MonoidAlgebra.single 1 (gramMatrix q u v) *
        orientedCoefficient T v l

/-- Rational scalars supported at the group identity are central. -/
theorem single_one_comm
    (T : TriangleIndex → Triangle (Generator := Generator))
    (c : ℚ) (a : RatGroupRing (Presented T)) :
    MonoidAlgebra.single 1 c * a = a * MonoidAlgebra.single 1 c := by
  change algebraMap ℚ (RatGroupRing (Presented T)) c * a =
    a * algebraMap ℚ (RatGroupRing (Presented T)) c
  exact Algebra.commutes c a

theorem single_one_mul_single_one
    (T : TriangleIndex → Triangle (Generator := Generator)) (a b : ℚ) :
    (MonoidAlgebra.single 1 a : RatGroupRing (Presented T)) *
        MonoidAlgebra.single 1 b = MonoidAlgebra.single 1 (a * b) := by
  rw [MonoidAlgebra.single_mul_single]
  simp only [one_mul]

theorem mul_mul_single_one
    (T : TriangleIndex → Triangle (Generator := Generator))
    (x y : RatGroupRing (Presented T)) (c : ℚ) :
    x * (y * MonoidAlgebra.single 1 c) =
      MonoidAlgebra.single 1 c * (x * y) := by
  rw [← mul_assoc, ← single_one_comm]

theorem single_one_one
    (T : TriangleIndex → Triangle (Generator := Generator)) :
    (MonoidAlgebra.single 1 (1 : ℚ) : RatGroupRing (Presented T)) = 1 := by
  rfl

theorem nested_mul_single_pair
    (T : TriangleIndex → Triangle (Generator := Generator))
    (x y : RatGroupRing (Presented T)) (a b : ℚ) :
    x * (y * (MonoidAlgebra.single 1 a * MonoidAlgebra.single 1 b)) =
      MonoidAlgebra.single 1 (a * b) * (x * y) := by
  rw [← mul_assoc, single_one_mul_single_one]
  exact (single_one_comm T (a * b) (x * y)).symm

/-- Scaling every Fox row by `1/d` scales its Gram matrix by `1/d²`. -/
theorem sum_scaledBoundary_gram
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (i l : Generator) :
    (∑ j, adjoint (scaledBoundary T regularDegree j i) *
      scaledBoundary T regularDegree j l) =
      MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree ^ 2) *
        (∑ j, adjoint (boundary T j i) * boundary T j l) := by
  have hterm (j : TriangleIndex) :
      adjoint (scaledBoundary T regularDegree j i) *
          scaledBoundary T regularDegree j l =
        MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree ^ 2) *
          (adjoint (boundary T j i) * boundary T j l) := by
    simp [scaledBoundary, ExactHodgeCertificate.adjoint_mul,
      single_one_comm, mul_assoc, pow_two]
  simp_rw [hterm]
  rw [← Finset.mul_sum]

/-- Rotate three finite summations without asking the simplifier to use the
permutative `sum_comm` rule globally. -/
theorem sum_comm_three {A B C M : Type*}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M]
    (f : A → B → C → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]

theorem adjoint_unscaledLinkRow {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (row : Row) (i : Generator) :
    adjoint (unscaledLinkRow T q row i) =
      ∑ u, adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1 (q row u) := by
  unfold unscaledLinkRow
  rw [adjoint_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [ExactHodgeCertificate.adjoint_mul, adjoint_single]
  simp only [inv_one]

theorem unscaledLinkRow_gram_row {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (row : Row) (i l : Generator) :
    adjoint (unscaledLinkRow T q row i) *
        unscaledLinkRow T q row l =
      ∑ u, ∑ v,
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1 (q row u * q row v) *
            orientedCoefficient T v l := by
  rw [adjoint_unscaledLinkRow]
  unfold unscaledLinkRow
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  simp [single_one_comm, mul_assoc]
  rw [mul_comm]

/-- Expanding the pulled-back rational rows gives the link Gram pullback. -/
theorem sum_unscaledLinkRow_gram {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (i l : Generator) :
    (∑ row, adjoint (unscaledLinkRow T q row i) *
      unscaledLinkRow T q row l) = linkGramPullback T q i l := by
  classical
  simp_rw [unscaledLinkRow_gram_row]
  rw [sum_comm_three]
  unfold linkGramPullback gramMatrix
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  exact congrArg
    (fun z : RatGroupRing (Presented T) ↦
      adjoint (orientedCoefficient T u i) * z *
        orientedCoefficient T v l)
    ((map_sum
      (MonoidAlgebra.singleAddHom (R := ℚ) (M := Presented T) 1)
      (fun row ↦ q row u * q row v) Finset.univ).symm)

/-- The `d` copies of rows scaled by `1/d` have total Gram coefficient
`1/d`. -/
theorem sum_liftedLinkRow_gram {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (hdegree : 0 < regularDegree)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (i l : Generator) :
    (∑ copyRow : Fin regularDegree × Row,
      adjoint (liftedLinkRow T regularDegree q copyRow.2 i) *
        liftedLinkRow T regularDegree q copyRow.2 l) =
      MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree) *
        linkGramPullback T q i l := by
  classical
  have hd : (regularDegree : ℚ) ≠ 0 := by exact_mod_cast hdegree.ne'
  have hterm (row : Row) :
      adjoint (liftedLinkRow T regularDegree q row i) *
          liftedLinkRow T regularDegree q row l =
        MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree ^ 2) *
          (adjoint (unscaledLinkRow T q row i) *
            unscaledLinkRow T q row l) := by
    simp [liftedLinkRow, ExactHodgeCertificate.adjoint_mul,
      single_one_comm, mul_assoc, pow_two]
  rw [Fintype.sum_prod_type]
  simp_rw [hterm]
  calc
    (∑ _copy : Fin regularDegree, ∑ row,
        MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree ^ 2) *
          (adjoint (unscaledLinkRow T q row i) *
            unscaledLinkRow T q row l)) =
        ∑ _copy : Fin regularDegree,
          MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree ^ 2) *
            linkGramPullback T q i l := by
      apply Finset.sum_congr rfl
      intro copy hcopy
      rw [← Finset.mul_sum, sum_unscaledLinkRow_gram]
    _ = MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree) *
          linkGramPullback T q i l := by
      rw [← Finset.sum_mul]
      congr 1
      simp only [Finset.sum_const, Fintype.card_fin]
      ext g
      by_cases hg : g = 1
      · subst g
        simp [hd]
        field_simp [hd]
      · simp [hg]

/-- The four internally chosen rows realize exactly the remaining multiple of
`D D⁺`. -/
theorem sum_coboundaryFactor_gram {Row : Type} [Fintype Row]
    {T : TriangleIndex → Triangle (Generator := Generator)}
    {regularDegree : ℕ} {gap : ℚ}
    {q : Row → SignedGenerator (Generator := Generator) → ℚ}
    (h : LinkCertificateChecks T regularDegree gap q) (i l : Generator) :
    (∑ k : Fin 4,
      adjoint (MonoidAlgebra.single 1 (coboundaryFactor h k) *
        adjoint (generatorCoboundary (generator T) i)) *
      (MonoidAlgebra.single 1 (coboundaryFactor h k) *
        adjoint (generatorCoboundary (generator T) l))) =
      MonoidAlgebra.single 1
          (garlandCoboundaryCoefficient
            (Generator := Generator) regularDegree gap) *
        (generatorCoboundary (generator T) i *
          adjoint (generatorCoboundary (generator T) l)) := by
  have hterm (k : Fin 4) :
      adjoint (MonoidAlgebra.single 1 (coboundaryFactor h k) *
          adjoint (generatorCoboundary (generator T) i)) *
        (MonoidAlgebra.single 1 (coboundaryFactor h k) *
          adjoint (generatorCoboundary (generator T) l)) =
        MonoidAlgebra.single 1 ((coboundaryFactor h k) ^ 2) *
          (generatorCoboundary (generator T) i *
            adjoint (generatorCoboundary (generator T) l)) := by
    simp [ExactHodgeCertificate.adjoint_mul, single_one_comm, mul_assoc,
      pow_two]
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  have hsum : (∑ k : Fin 4,
      (MonoidAlgebra.single 1 ((coboundaryFactor h k) ^ 2) :
        RatGroupRing (Presented T))) =
        (MonoidAlgebra.single 1
          (garlandCoboundaryCoefficient
            (Generator := Generator) regularDegree gap) :
          RatGroupRing (Presented T)) := by
    have hmap :
        (∑ k : Fin 4,
          (MonoidAlgebra.singleAddHom (R := ℚ)
            (M := Presented T) 1) ((coboundaryFactor h k) ^ 2)) =
          (MonoidAlgebra.singleAddHom (R := ℚ)
            (M := Presented T) 1)
            (∑ k : Fin 4, (coboundaryFactor h k) ^ 2) :=
      (map_sum
        (MonoidAlgebra.singleAddHom (R := ℚ) (M := Presented T) 1)
        (fun k : Fin 4 ↦ (coboundaryFactor h k) ^ 2)
        Finset.univ).symm
    have hsquare := congrArg
      (MonoidAlgebra.singleAddHom (R := ℚ) (M := Presented T) 1)
      (sum_sq_coboundaryFactor h)
    exact hmap.trans hsquare
  exact congrArg (fun z : RatGroupRing (Presented T) ↦
    z * (generatorCoboundary (generator T) i *
      adjoint (generatorCoboundary (generator T) l))) hsum

/-- Pullback of the identity matrix on signed-link coordinates. -/
theorem signedIdentity_pullback
    (T : TriangleIndex → Triangle (Generator := Generator)) (i l : Generator) :
    (∑ u, ∑ v,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1 (if u = v then (1 : ℚ) else 0) *
          orientedCoefficient T v l) =
      if i = l then MonoidAlgebra.single 1 2 else 0 := by
  classical
  have hdiag := sum_adjoint_orientedCoefficient_mul T i l
  have hrow (u : SignedGenerator (Generator := Generator)) :
      (∑ v,
        adjoint (orientedCoefficient T u i) *
          MonoidAlgebra.single 1 (if u = v then (1 : ℚ) else 0) *
            orientedCoefficient T v l) =
        adjoint (orientedCoefficient T u i) *
          orientedCoefficient T u l := by
    have hterm (v : SignedGenerator (Generator := Generator)) :
        adjoint (orientedCoefficient T u i) *
            MonoidAlgebra.single 1 (if u = v then (1 : ℚ) else 0) *
              orientedCoefficient T v l =
          if v = u then
            adjoint (orientedCoefficient T u i) *
              orientedCoefficient T v l else 0 := by
      by_cases hvu : v = u
      · subst v
        rw [if_pos rfl, if_pos rfl]
        have hone :
            (MonoidAlgebra.single 1 1 : RatGroupRing (Presented T)) = 1 := by
          simp [MonoidAlgebra.one_def]
        rw [hone, mul_one]
      · have huv : u ≠ v := fun huv ↦ hvu huv.symm
        simp [hvu, huv]
    simp_rw [hterm]
    rw [Fintype.sum_ite_eq']
  simp_rw [hrow]
  exact hdiag

/-- Pullback of a constant scalar matrix factors as the product of the two
signed-coordinate sums. -/
theorem signedConstant_pullback
    (T : TriangleIndex → Triangle (Generator := Generator))
    (c : ℚ) (i l : Generator) :
    (∑ u, ∑ v,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1 c * orientedCoefficient T v l) =
      MonoidAlgebra.single 1 c *
        (generatorCoboundary (generator T) i *
          adjoint (generatorCoboundary (generator T) l)) := by
  classical
  simp_rw [← Finset.mul_sum]
  simp_rw [mul_assoc]
  rw [← Finset.sum_mul]
  rw [sum_orientedCoefficient]
  rw [← adjoint_sum, sum_orientedCoefficient]
  simp only [adjoint_neg, adjoint_adjoint, neg_mul, mul_neg, neg_neg]
  rw [← mul_assoc, ← single_one_comm, mul_assoc]

/-- Pullback of the mean-zero projector. -/
theorem meanZeroProjector_pullback
    (T : TriangleIndex → Triangle (Generator := Generator)) (i l : Generator) :
    (∑ u, ∑ v,
      adjoint (orientedCoefficient T u i) *
        MonoidAlgebra.single 1 (meanZeroProjector u v) *
          orientedCoefficient T v l) =
      (if i = l then MonoidAlgebra.single 1 2 else 0) -
        MonoidAlgebra.single 1
          ((1 : ℚ) /
            Fintype.card (SignedGenerator (Generator := Generator))) *
          (generatorCoboundary (generator T) i *
            adjoint (generatorCoboundary (generator T) l)) := by
  classical
  simp only [meanZeroProjector, MonoidAlgebra.single_sub, mul_sub, sub_mul,
    Finset.sum_sub_distrib]
  rw [signedIdentity_pullback, signedConstant_pullback]

noncomputable def pulledScalarEntry
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i l : Generator)
    (u v : SignedGenerator (Generator := Generator)) (c : ℚ) :
    RatGroupRing (Presented T) :=
  adjoint (orientedCoefficient T u i) *
    MonoidAlgebra.single 1 c * orientedCoefficient T v l

theorem single_mul_pulledScalarEntry
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i l : Generator)
    (u v : SignedGenerator (Generator := Generator)) (a c : ℚ) :
    MonoidAlgebra.single 1 a * pulledScalarEntry T i l u v c =
      pulledScalarEntry T i l u v (a * c) := by
  simp [pulledScalarEntry, single_one_comm, mul_assoc]
  rw [mul_comm]

theorem pulledScalarEntry_add
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i l : Generator)
    (u v : SignedGenerator (Generator := Generator)) (a b : ℚ) :
    pulledScalarEntry T i l u v a + pulledScalarEntry T i l u v b =
      pulledScalarEntry T i l u v (a + b) := by
  simp [pulledScalarEntry, MonoidAlgebra.single_add, mul_add, add_mul]

theorem single_mul_pulledScalarSum
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i l : Generator) (a : ℚ)
    (m : SignedGenerator (Generator := Generator) →
      SignedGenerator (Generator := Generator) → ℚ) :
    MonoidAlgebra.single 1 a * (∑ u, ∑ v, pulledScalarEntry T i l u v (m u v)) =
      ∑ u, ∑ v, pulledScalarEntry T i l u v (a * m u v) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact single_mul_pulledScalarEntry T i l u v a (m u v)

theorem sum_two_components {A B M : Type*}
    [Fintype A] [Fintype B] [AddCommMonoid M]
    (a b : A → B → M) :
    (∑ x, ∑ y, a x y) + (∑ x, ∑ y, b x y) =
      ∑ x, ∑ y, (a x y + b x y) := by
  simp only [Finset.sum_add_distrib]

/-- Pulling back the checked normalized link identity. -/
theorem normalizedLink_pullback {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (h : LinkCertificateChecks T regularDegree gap q) (i l : Generator) :
    MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree ^ 2) *
        linkLaplacianPullback T i l =
      MonoidAlgebra.single 1 (gap / regularDegree) *
        (∑ u, ∑ v,
          adjoint (orientedCoefficient T u i) *
            MonoidAlgebra.single 1 (meanZeroProjector u v) *
              orientedCoefficient T v l) +
      MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree) *
        linkGramPullback T q i l := by
  classical
  have hd : (regularDegree : ℚ) ≠ 0 := by exact_mod_cast h.1.ne'
  change MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree ^ 2) *
      (∑ u, ∑ v, pulledScalarEntry T i l u v
        (rationalLinkLaplacian T u v)) =
    MonoidAlgebra.single 1 (gap / regularDegree) *
      (∑ u, ∑ v, pulledScalarEntry T i l u v
        (meanZeroProjector u v)) +
    MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree) *
      (∑ u, ∑ v, pulledScalarEntry T i l u v
        (gramMatrix q u v))
  rw [single_mul_pulledScalarSum, single_mul_pulledScalarSum,
    single_mul_pulledScalarSum, sum_two_components]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [pulledScalarEntry_add]
  apply congrArg (pulledScalarEntry T i l u v)
  have hid := linkGap_identity_of_checks h u v
  field_simp [hd] at hid ⊢
  linarith

theorem garlandDecomposition {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (h : LinkCertificateChecks T regularDegree gap q) (i l : Generator) :
    hodgeMatrix (generatorCoboundary (generator T))
        (scaledBoundary T regularDegree) i l =
      scalarMatrix (garlandGap regularDegree gap) i l +
        (∑ a, adjoint (garlandGramRow T regularDegree gap q h a i) *
          garlandGramRow T regularDegree gap q h a l) + 0 := by
  classical
  unfold hodgeMatrix
  rw [sum_scaledBoundary_gram]
  have hglobal := linkLaplacianPullback_eq_boundaryGram_add_diagonal
    T regularDegree h.2.2.1 i l
  rw [show (∑ j, adjoint (boundary T j i) * boundary T j l) =
      linkLaplacianPullback T i l -
        (if i = l then MonoidAlgebra.single 1 (regularDegree : ℚ) else 0) by
    rw [hglobal]
    noncomm_ring]
  simp only [garlandGramRow, GarlandRow, Fintype.sum_sum_type]
  rw [mul_sub]
  rw [sum_liftedLinkRow_gram T regularDegree h.1 q i l,
    sum_coboundaryFactor_gram h i l,
    normalizedLink_pullback T regularDegree gap q h i l,
    meanZeroProjector_pullback]
  have hdQ : (regularDegree : ℚ) ≠ 0 := by
    exact_mod_cast h.1.ne'
  have hNQ :
      (Fintype.card (SignedGenerator (Generator := Generator)) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (SignedGenerator (Generator := Generator)) ≠ 0)
  have hmeanScalar :
      ((1 : ℚ) / Fintype.card (SignedGenerator (Generator := Generator))) *
          (gap / regularDegree) =
        gap / (Fintype.card (SignedGenerator (Generator := Generator)) *
          regularDegree) := by
    field_simp [hdQ, hNQ]
  have hdiagonalScalar :
      (2 : ℚ) * (gap / regularDegree) -
          ((1 : ℚ) / regularDegree ^ 2) * regularDegree =
        (2 * gap - 1) / regularDegree := by
    field_simp [hdQ]
  have hGeneratorQ : (Fintype.card Generator : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Generator ≠ 0)
  have hcardSigned :
      (Fintype.card (SignedGenerator (Generator := Generator)) : ℚ) =
        2 * (Fintype.card Generator : ℚ) := by
    simp [SignedGenerator, Fintype.card_prod, mul_comm]
  have hmeanExpanded :
      (2 : ℚ)⁻¹ * (Fintype.card Generator : ℚ)⁻¹ *
          (gap / regularDegree) =
        gap / (2 * ((Fintype.card Generator : ℚ) * regularDegree)) := by
    field_simp [hdQ, hGeneratorQ]
  have hdiagonalExpanded :
      (2 : ℚ) * (gap / regularDegree) -
          ((regularDegree : ℚ) * regularDegree)⁻¹ * regularDegree =
        (2 * gap - 1) / regularDegree := by
    field_simp [hdQ]
  by_cases hil : i = l
  · subst l
    simp [garlandCoboundaryCoefficient, garlandGap, scalarMatrix,
      single_one_comm, hcardSigned, hmeanScalar, hmeanExpanded,
      hdiagonalScalar, hdiagonalExpanded]
    rw [sub_mul]
    simp_rw [mul_assoc, single_one_mul_single_one]
    rw [hmeanExpanded]
    have hdiagonalSingle :
        MonoidAlgebra.single (M := Presented T) 1
              (2 * (gap / regularDegree)) -
            MonoidAlgebra.single 1
              (((regularDegree : ℚ) ^ 2)⁻¹ * regularDegree) =
          MonoidAlgebra.single 1 ((2 * gap - 1) / regularDegree) := by
      rw [← MonoidAlgebra.single_sub]
      congr 1
      simpa [pow_two] using hdiagonalExpanded
    have hdiagonalAdd := sub_eq_iff_eq_add.mp hdiagonalSingle
    rw [hdiagonalAdd]
    rw [mul_mul_single_one T, single_one_one T]
    noncomm_ring
  · simp [garlandCoboundaryCoefficient, garlandGap, scalarMatrix,
      single_one_comm, hil, hcardSigned, hmeanScalar, hmeanExpanded]
    simp_rw [mul_assoc, single_one_mul_single_one]
    rw [hmeanExpanded]
    rw [mul_mul_single_one T, single_one_one T]
    noncomm_ring

/-- The exact Garland/Żuk certificate assembled entirely from finite link
data.  There is no analytic or literature premise: all rows are explicit
rational group-ring expressions. -/
theorem garlandCertificate {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (h : LinkCertificateChecks T regularDegree gap q) :
    Certificate
      (generatorCoboundary (generator T))
      (scaledBoundary T regularDegree)
      (garlandGramRow T regularDegree gap q h)
      (fun _ _ ↦ 0) (garlandGap regularDegree gap) 0 := by
  classical
  have hl1zero :
      l1 (0 : RatGroupRing (Presented T)) = 0 := by
    simp [l1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hd : (0 : ℚ) < regularDegree := by exact_mod_cast h.1
    have hg : (1 : ℚ) < 2 * gap := by linarith [h.2.1]
    simp [garlandGap]
    exact div_pos (sub_pos.mpr hg) hd
  · intro j
    unfold scaledBoundary
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [boundary_chain]
    simp
  · intro i l
    exact garlandDecomposition T regularDegree gap q h i l
  · intro i
    simp [hl1zero]
  · intro l
    simp [hl1zero]

/-- A checked exact regular triangular-link table above the one-half threshold
gives property `(T)` for its presented group. -/
theorem presented_hasKazhdanPropertyT_of_linkCertificate
    {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (h : LinkCertificateChecks T regularDegree gap q) :
    HasKazhdanPropertyT.{0, 0} (Presented T) := by
  let C : Certificate
      (generatorCoboundary (generator T))
      (scaledBoundary T regularDegree)
      (garlandGramRow T regularDegree gap q h)
      (fun _ _ ↦ 0) (garlandGap regularDegree gap) 0 :=
    garlandCertificate T regularDegree gap q h
  have hgen : Subgroup.closure (Set.range (generator T)) = ⊤ :=
    closure_range_generator T
  exact Certificate.hasKazhdanPropertyT
    (inferInstance : Nonempty Generator) (generator T) hgen C

end SpectralCertificate

end GroupApproximation.TriangularHodgeLayer
