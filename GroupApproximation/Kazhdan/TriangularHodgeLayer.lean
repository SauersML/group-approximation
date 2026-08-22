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

abbrev SignedGenerator := Generator × Bool
abbrev Triangle := Fin 3 → SignedGenerator

def letters (t : Triangle (Generator := Generator)) : SignedWord Generator :=
  List.ofFn t

def relator (t : Triangle (Generator := Generator)) : FreeGroup Generator :=
  word (letters t)

def relators (T : TriangleIndex → Triangle (Generator := Generator)) :
    Finset (FreeGroup Generator) :=
  Finset.univ.image (relator ∘ T)

abbrev Presented (T : TriangleIndex → Triangle (Generator := Generator)) :=
  PresentedGroup (relators T : Set (FreeGroup Generator))

def generator (T : TriangleIndex → Triangle (Generator := Generator)) :
    Generator → Presented T := PresentedGroup.of

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
  rw [wordValue_freeGroup_map
    (PresentedGroup.mk (relators T : Set (FreeGroup Generator)))]
  exact PresentedGroup.one_of_mem (relator_mem T j)

/-- Every triangular Fox row satisfies the exact chain equation consumed by
the Hodge certificate. -/
theorem boundary_chain
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) :
    ∑ i, boundary T j i * generatorCoboundary (generator T) i = 0 := by
  rw [FoxBoundary.sum_boundary_mul_coboundary,
    wordValue_triangle_eq_one T j]
  simp

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
  simpa [cornerValue, letters, wordValue, List.ofFn] using
    wordValue_triangle_eq_one T j

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
      cornerBoundaryCoefficient, cornerPrefix, cornerValue, letters,
      List.ofFn, h0, h1, h2, Fin.sum_univ_succ]

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
  · simp [linkLaplacian, h, h.symm, adjacencyCount_comm]

/-- Every row of the exact link Laplacian sums to zero. -/
theorem linkLaplacian_row_sum
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u : SignedGenerator (Generator := Generator)) :
    ∑ v, linkLaplacian T u v = 0 := by
  classical
  simp only [linkLaplacian, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq' Finset.univ u]
  simp [degree]

/-- Rational form used by exact spectral/Gram computations. -/
def rationalLinkLaplacian
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u v : SignedGenerator (Generator := Generator)) : ℚ :=
  linkLaplacian T u v

theorem rationalLinkLaplacian_row_sum
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u : SignedGenerator (Generator := Generator)) :
    ∑ v, rationalLinkLaplacian T u v = 0 := by
  rw [← Int.cast_sum, linkLaplacian_row_sum]
  simp

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
  simp_rw [Fintype.sum_bool, orientedCoefficient_pair_sum, add_comm]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp

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
    simp [orientedCoefficient]
  · simp [orientedCoefficient, h, h.symm]

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

/-- Local Garland identity before taking a Gram product: a pulled-back link
edge difference is a unit translate of the sum of its adjacent Fox corners. -/
theorem edgeDifference_eq_translation_mul_corner_sum
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) (i : Generator) :
    edgeDifference T j k i =
      edgeTranslationUnit T j k *
        (cornerBoundaryCoefficient T j k i +
          cornerBoundaryCoefficient T j (nextCorner k) i) := by
  classical
  have hprod := cornerValue_mul_cornerValue_mul_cornerValue T j
  rcases h0 : T j 0 with ⟨g0, s0⟩
  rcases h1 : T j 1 with ⟨g1, s1⟩
  rcases h2 : T j 2 with ⟨g2, s2⟩
  fin_cases k <;> cases s0 <;> cases s1 <;> cases s2 <;>
    simp_all [edgeDifference, edgeTranslationUnit, orientedCoefficient,
      inverseSigned, nextCorner, cornerBoundaryCoefficient, cornerPrefix,
      cornerValue, h0, h1, h2] <;> group

/-- The translating coefficient is unitary in the rational group ring. -/
theorem adjoint_edgeTranslationUnit_mul_self
    (T : TriangleIndex → Triangle (Generator := Generator))
    (j : TriangleIndex) (k : Fin 3) :
    adjoint (edgeTranslationUnit T j k) * edgeTranslationUnit T j k = 1 := by
  simp [edgeTranslationUnit]

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
  simp [adjoint_mul, mul_assoc, adjoint_edgeTranslationUnit_mul_self]

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
  cases s <;>
    simp [cornerBoundaryCoefficient, cornerValue, h, mul_assoc]

/-- Pullback of the exact rational link Laplacian along the signed-coordinate
matrix. -/
noncomputable def linkLaplacianPullback
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i l : Generator) : RatGroupRing (Presented T) :=
  ∑ u, ∑ v,
    adjoint (orientedCoefficient T u i) *
      MonoidAlgebra.single 1 (rationalLinkLaplacian T u v) *
        orientedCoefficient T v l

/-- Incidence-matrix identity for the corrected link multigraph: its
Laplacian pullback is the sum of the three literal edge-difference Gram
matrices.  Exact directed multiplicities make this valid for loops and
coincident orientations as well. -/
theorem linkLaplacianPullback_eq_sum_edgeDifference
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i l : Generator) :
    linkLaplacianPullback T i l =
      ∑ j, ∑ k : Fin 3,
        adjoint (edgeDifference T j k i) * edgeDifference T j k l := by
  classical
  simp [linkLaplacianPullback, rationalLinkLaplacian, linkLaplacian,
    degree, adjacencyCount, directedAdjacencyCount, edgeDifference,
    Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, sub_eq_add_neg]
  noncomm_ring

/-- Number of literal occurrences of an underlying generator. -/
def generatorOccurrenceCount
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i : Generator) : ℕ :=
  ((Finset.univ : Finset (TriangleIndex × Fin 3)).filter fun p ↦
    (T p.1 p.2).1 = i).card

/-- The degree of either signed vertex is the total number of occurrences of
its underlying generator.  Cyclic successor is a permutation of the three
corners, so incoming and outgoing directed counts partition the two signs. -/
theorem degree_eq_generatorOccurrenceCount
    (T : TriangleIndex → Triangle (Generator := Generator))
    (i : Generator) (sign : Bool) :
    degree T (i, sign) = generatorOccurrenceCount T i := by
  classical
  simp [degree, adjacencyCount, directedAdjacencyCount,
    generatorOccurrenceCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    inverseSigned, nextCorner, Fin.sum_univ_succ]

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
    simp [generatorOccurrenceCount, Finset.card_eq_sum_ones,
      Finset.sum_filter, eq_comm]
  · simp [h]

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

instance instDecidableLinkCertificateChecks {Row : Type}
    [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ) :
    Decidable (LinkCertificateChecks T regularDegree gap q) := inferInstance

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

/-- Pull one rational link-Gram row back to generator coordinates, scaled by
`1/d`.  Taking `d` identical copies produces the required coefficient `1/d`
without a square root. -/
noncomputable def liftedLinkRow {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (row : Row) (i : Generator) : RatGroupRing (Presented T) :=
  ∑ u, MonoidAlgebra.single 1 (q row u / regularDegree) *
    orientedCoefficient T u i

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
    simp [n, Fintype.card_prod]
  have hn : (2 : ℚ) ≤ n := by exact_mod_cast hnNat
  have hP : (1 : ℚ) / 2 ≤ meanZeroProjector u u := by
    simp [meanZeroProjector, n] at hn ⊢
    have hnpos : (0 : ℚ) < n := lt_of_lt_of_le (by norm_num) hn
    have hinv := (div_le_div_iff_of_pos_left (by norm_num : (0 : ℚ) < 1)
      hnpos (by norm_num : (0 : ℚ) < 2)).2 hn
    linarith
  have hGram : 0 ≤ gramMatrix q u u := by
    exact Finset.sum_nonneg fun row _ ↦ sq_nonneg (q row u)
  have hLle : rationalLinkLaplacian T u u / regularDegree ≤ 1 := by
    unfold rationalLinkLaplacian linkLaplacian
    simp only [if_pos]
    have ha : (0 : ℚ) ≤ adjacencyCount T u u := by positivity
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
  refine ⟨?_, ?_, ?_, by simp, by simp⟩
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
    unfold hodgeMatrix
    rw [show (∑ j,
        adjoint (scaledBoundary T regularDegree j i) *
          scaledBoundary T regularDegree j l) =
        MonoidAlgebra.single 1 ((1 : ℚ) / regularDegree ^ 2) *
          (∑ j, adjoint (boundary T j i) * boundary T j l) by
      simp [scaledBoundary, Finset.mul_sum, adjoint_mul, mul_assoc]
      noncomm_ring]
    have hglobal := linkLaplacianPullback_eq_boundaryGram_add_diagonal
      T regularDegree h.2.2.1 i l
    rw [show (∑ j, adjoint (boundary T j i) * boundary T j l) =
        linkLaplacianPullback T i l -
          (if i = l then MonoidAlgebra.single 1 (regularDegree : ℚ) else 0) by
      rw [hglobal]
      noncomm_ring]
    simp only [garlandGramRow, GarlandRow, Fintype.sum_sum_type,
      Fintype.sum_prod_type]
    rw [sum_sq_coboundaryFactor h]
    simp [liftedLinkRow, linkLaplacianPullback,
      linkGap_identity_of_checks h, gramMatrix, meanZeroProjector,
      garlandCoboundaryCoefficient, garlandGap, scalarMatrix,
      Finset.mul_sum, Finset.sum_mul, adjoint_sum, adjoint_mul, mul_assoc]
    noncomm_ring

/-- A checked exact regular triangular-link table above the one-half threshold
gives property `(T)` for its presented group. -/
theorem presented_hasKazhdanPropertyT_of_linkCertificate
    {Row : Type} [Fintype Row]
    (T : TriangleIndex → Triangle (Generator := Generator))
    (regularDegree : ℕ) (gap : ℚ)
    (q : Row → SignedGenerator (Generator := Generator) → ℚ)
    (h : LinkCertificateChecks T regularDegree gap q) :
    HasKazhdanPropertyT.{0, 0} (Presented T) :=
  Certificate.hasKazhdanPropertyT (inferInstance : Nonempty Generator)
    (generator T) (PresentedGroup.closure_range_of (relators T : Set _))
    (garlandCertificate T regularDegree gap q h)

end SpectralCertificate

end GroupApproximation.TriangularHodgeLayer
