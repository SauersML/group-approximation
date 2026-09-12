import Mathlib.Data.Nat.Notation
import GroupApproximation.Meta.AxiomGuard

/-!
# The numeric curvature count for angled triangular discs

`TriangularDiscCounts` (`KazhdanHypGirthEightDiagram`) is the count behind the
`C(3)`–`T(8)` inequality `F + 8 ≤ 3B`.  This file records the analogous count
for triangles with corner angles `π/3, π/4, π/4`, as in the `(6,8,8)` triangle of
groups of `GHB(p)`.  In units of `π/12` the three corners of a face carry
`4 + 3 + 3 = 10`, and an interior vertex whose link circuits have girth `6` at
type-`0` vertices and `8` at the other two types receives at least `24 = 2π`.
So the total angle bound reads `24 I ≤ 10 F`.

The record is independent of any diagram encoding.  Its fields are the counts
`V E F B V∂ I` of a disc (inner faces only, `B` the outer-face degree, `V∂` the
vertices on the outer boundary, `I` the others) and the relations

* `V∂ ≤ B`, `I = V - V∂`;
* Euler: `V + F = E + 1`;
* face incidence: `2E = 3F + B`;
* angle bound: `24 I ≤ 10 F`.

`faceCount_add_twelve_le_six_mul_boundaryLength` proves `F + 12 ≤ 6B`: Euler and
face incidence give `2V = F + B + 2`, so `2I ≥ F - B + 2`, and the angle bound
gives `12 (F - B + 2) ≤ 10 F`.  `sharpModel` attains equality, so the constants
cannot be improved from these relations.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

/-- The six counts and five relations of the angled triangular curvature count. -/
structure TypedTriangularDiscCounts where
  /-- All vertices of the disc. -/
  vertexCount : ℕ
  /-- Edges of the disc. -/
  edgeCount : ℕ
  /-- Inner triangular faces. -/
  faceCount : ℕ
  /-- Degree of the outer face. -/
  boundaryLength : ℕ
  /-- Vertices incident to the outer face. -/
  boundaryVertexCount : ℕ
  /-- Vertices not incident to the outer face. -/
  interiorVertexCount : ℕ
  /-- A boundary circuit visits at least as many darts as distinct vertices. -/
  boundaryVertexCount_le : boundaryVertexCount ≤ boundaryLength
  /-- The interior vertices are the vertices off the boundary. -/
  interiorVertexCount_eq : interiorVertexCount = vertexCount - boundaryVertexCount
  /-- Euler's formula for the disc, `V - E + F = 1`. -/
  euler : vertexCount + faceCount = edgeCount + 1
  /-- The sum of the degrees of all faces, the outer one included. -/
  faceIncidence : 2 * edgeCount = 3 * faceCount + boundaryLength
  /-- Angle bound in units of `π/12`: each face carries `10`, each interior
  vertex receives at least `24`. -/
  angleLower : 24 * interiorVertexCount ≤ 10 * faceCount

namespace TypedTriangularDiscCounts

/-- **Angled triangular curvature inequality**, `F + 12 ≤ 6B`. -/
theorem faceCount_add_twelve_le_six_mul_boundaryLength (C : TypedTriangularDiscCounts) :
    C.faceCount + 12 ≤ 6 * C.boundaryLength := by
  have hb := C.boundaryVertexCount_le
  have hi := C.interiorVertexCount_eq
  have he := C.euler
  have hf := C.faceIncidence
  have ha := C.angleLower
  omega

/-- The homogeneous linear bound, `F ≤ 6B`. -/
theorem faceCount_le_six_mul_boundaryLength (C : TypedTriangularDiscCounts) :
    C.faceCount ≤ 6 * C.boundaryLength := by
  have h := C.faceCount_add_twelve_le_six_mul_boundaryLength
  omega

/-- Every record has boundary length at least two. -/
theorem two_le_boundaryLength (C : TypedTriangularDiscCounts) : 2 ≤ C.boundaryLength := by
  have h := C.faceCount_add_twelve_le_six_mul_boundaryLength
  omega

/-- The one-triangle disc: three vertices and edges, one face, no interior vertex. -/
def oneTriangle : TypedTriangularDiscCounts where
  vertexCount := 3
  edgeCount := 3
  faceCount := 1
  boundaryLength := 3
  boundaryVertexCount := 3
  interiorVertexCount := 0
  boundaryVertexCount_le := by omega
  interiorVertexCount_eq := by omega
  euler := by omega
  faceIncidence := by omega
  angleLower := by omega

/-- A record attaining equality in `F + 12 ≤ 6B`: `V = 9`, `E = 20`, `F = 12`,
`B = V∂ = 4`, `I = 5`, with `24 I = 10 F`. -/
def sharpModel : TypedTriangularDiscCounts where
  vertexCount := 9
  edgeCount := 20
  faceCount := 12
  boundaryLength := 4
  boundaryVertexCount := 4
  interiorVertexCount := 5
  boundaryVertexCount_le := by omega
  interiorVertexCount_eq := by omega
  euler := by omega
  faceIncidence := by omega
  angleLower := by omega

/-- The additive constant twelve is sharp for the record. -/
theorem sharpModel_equality :
    sharpModel.faceCount + 12 = 6 * sharpModel.boundaryLength := rfl

end TypedTriangularDiscCounts

end VanKampen
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.VanKampen.TypedTriangularDiscCounts.faceCount_add_twelve_le_six_mul_boundaryLength
#audit_axioms GroupApproximation.GGT.VanKampen.TypedTriangularDiscCounts.faceCount_le_six_mul_boundaryLength
#audit_axioms GroupApproximation.GGT.VanKampen.TypedTriangularDiscCounts.sharpModel_equality
