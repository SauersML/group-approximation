import GroupApproximation.Kazhdan.FoxBoundary
import GroupApproximation.Kazhdan.FiniteSupportHodgeCertificate
import Mathlib.Data.Fin.Tuple.Reflection

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

/-! ## The finite directed link matrix -/

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

/-- Out-degree, with multiplicities, in the directed link. -/
def degree
    (T : TriangleIndex → Triangle (Generator := Generator))
    (u : SignedGenerator (Generator := Generator)) : ℕ :=
  ∑ v, adjacencyCount T u v

/-- Integral directed link Laplacian `D - A`. -/
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

/-! ## Exact rational spectral-certificate tables -/

section SpectralCertificate

variable [Nonempty Generator]

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

end SpectralCertificate

end GroupApproximation.TriangularHodgeLayer
