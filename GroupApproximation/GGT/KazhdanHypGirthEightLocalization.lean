import GroupApproximation.GGT.KazhdanHypGirthEightTorsion
import GroupApproximation.GGT.KazhdanHypGirthEightFromDiagram

/-!
# Spherical curvature for girth-eight triangle presentations

Huebschmann, *Cohomology theory of aspherical groups and of small cancellation
groups*, Journal of Pure and Applied Algebra 14 (1979), Theorem 4, proves that
every `C(3)`--`T(6)` presentation is aspherical.  The result is quoted in
Karol Duda, *Torsion subgroups of small cancellation groups*,
arXiv:2112.01912, section `Proof of Theorem A`, `all3.tex` lines 1234--1241.
Duda first defines a spherical diagram as a combinatorial two-sphere mapping
to the presentation complex, then quotes Huebschmann's asphericity theorem.

This file proves the Euler-curvature part of that theorem for a triangular
spherical map.  If every face has degree three and every vertex has degree at
least six, the three incidence identities imply a contradiction.  The proof
uses the closed combinatorial maps in `VanKampen.CombMap` and is independent
of the disc-boundary estimate.

The final section connects this curvature obstruction to the finite-order
localization interface from `KazhdanHypGirthEightTorsion`.  Its premise is not
a renamed localization assertion: it asks for a concrete reduced spherical
map with triangular faces and vertex degree at least eight from a finite-order
element when no proper-power relator exists.  Building that map is the exact
topological primitive still absent from the current van Kampen library.
Huebschmann's Theorem 3, quoted at Duda `all3.tex` lines 1243--1248, supplies
the stronger root, divisibility, and conjugacy conclusion once asphericity is
known.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open scoped BigOperators

/-! ## The numerical spherical curvature identity -/

/-- Numerical data read from a triangular cellulation of a two-sphere.
`minimumDegree` is a lower bound for every vertex degree. -/
structure TriangularSphereCounts (minimumDegree : ℕ) where
  /-- Number of vertices. -/
  vertexCount : ℕ
  /-- Number of edges. -/
  edgeCount : ℕ
  /-- Number of triangular faces. -/
  faceCount : ℕ
  /-- Euler's identity for the two-sphere. -/
  euler : vertexCount + faceCount = edgeCount + 2
  /-- Each edge occurs in the boundaries of two triangular faces. -/
  faceIncidence : 2 * edgeCount = 3 * faceCount
  /-- The vertex-degree sum is at least the prescribed lower bound. -/
  vertexIncidence : minimumDegree * vertexCount ≤ 2 * edgeCount

namespace TriangularSphereCounts

/-- The tetrahedral counts are the smallest standard triangular sphere and
give a direct model of the count interface at minimum degree three. -/
def tetrahedron : TriangularSphereCounts 3 where
  vertexCount := 4
  edgeCount := 6
  faceCount := 4
  euler := by norm_num
  faceIncidence := by norm_num
  vertexIncidence := by norm_num

/-- At the tetrahedral base index the vertex incidence bound is an equality,
not a weakened estimate. -/
theorem tetrahedron_vertexIncidence_eq :
    3 * tetrahedron.vertexCount = 2 * tetrahedron.edgeCount := by
  norm_num [tetrahedron]

/-- A triangular two-sphere cannot have minimum vertex degree six.  Euler's
identity and the face incidence identity give
`2 * vertexCount = faceCount + 4`, while the vertex bound gives
`2 * vertexCount ≤ faceCount`. -/
theorem false_of_six_le {minimumDegree : ℕ}
    (C : TriangularSphereCounts minimumDegree)
    (hdegree : 6 ≤ minimumDegree) : False := by
  have heuler := C.euler
  have hface := C.faceIncidence
  have hvertex := C.vertexIncidence
  have hsix : 6 * C.vertexCount ≤ 2 * C.edgeCount :=
    (Nat.mul_le_mul_right C.vertexCount hdegree).trans hvertex
  omega

/-- Degree six is the sharp threshold used by the `C(3)`--`T(6)` spherical
curvature argument. -/
theorem not_nonempty_six : ¬ Nonempty (TriangularSphereCounts 6) := by
  rintro ⟨C⟩
  exact C.false_of_six_le (by norm_num)

end TriangularSphereCounts

/-! ## Counts extracted from a closed combinatorial map -/

/-- A closed planar combinatorial map with triangular faces and a uniform
lower bound on vertex degree.  For a reduced spherical diagram over a
`C(3)`--`T(q)` presentation, the presentation supplies these two local degree
conditions. -/
structure TriangularSphericalMap
    (minimumDegree : ℕ) (M : CombMap) where
  /-- The underlying closed surface is a combinatorial two-sphere. -/
  planar : M.IsPlanar
  /-- Every face is triangular. -/
  faceDegree : ∀ f : M.Face, M.faceDegree f = 3
  /-- Every vertex has degree at least `minimumDegree`. -/
  vertexDegree : ∀ v : M.Vertex, minimumDegree ≤ M.vertexDegree v

namespace TriangularSphericalMap

variable {minimumDegree : ℕ} {M : CombMap}

/-- Lowering the minimum-degree parameter preserves a triangular spherical
map.  In particular, the `T(8)` local estimate contains the `T(6)` estimate
used in Huebschmann's asphericity theorem. -/
theorem weaken {smallerDegree : ℕ}
    (C : TriangularSphericalMap minimumDegree M)
    (hdegree : smallerDegree ≤ minimumDegree) :
    TriangularSphericalMap smallerDegree M where
  planar := C.planar
  faceDegree := C.faceDegree
  vertexDegree := fun v ↦ hdegree.trans (C.vertexDegree v)

/-- Euler's identity in natural-number cardinalities. -/
theorem euler_count (C : TriangularSphericalMap minimumDegree M) :
    M.vertexCount + M.faceCount = M.edgeCount + 2 := by
  have heulerInt : (M.vertexCount : ℤ) + (M.faceCount : ℤ) =
      (M.edgeCount : ℤ) + 2 := by
    have heuler := M.euler_eq_two C.planar
    linarith
  exact_mod_cast heulerInt

/-- The triangular face-degree sum gives `2 E = 3 F`. -/
theorem face_incidence (C : TriangularSphericalMap minimumDegree M) :
    2 * M.edgeCount = 3 * M.faceCount := by
  classical
  have hsum : 3 * M.faceCount = 2 * M.edgeCount := by
    calc
      3 * M.faceCount = ∑ _f : M.Face, 3 := by
        simp [CombMap.faceCount, Nat.mul_comm]
      _ = ∑ f : M.Face, M.faceDegree f := by
        apply Finset.sum_congr rfl
        intro f _
        exact (C.faceDegree f).symm
      _ = 2 * M.edgeCount := M.sum_faceDegree_eq_two_mul_edgeCount
  exact hsum.symm

/-- The lower vertex-degree bound gives `q V ≤ 2 E`. -/
theorem vertex_incidence (C : TriangularSphericalMap minimumDegree M) :
    minimumDegree * M.vertexCount ≤ 2 * M.edgeCount := by
  classical
  calc
    minimumDegree * M.vertexCount = ∑ _v : M.Vertex, minimumDegree := by
      simp [CombMap.vertexCount, Nat.mul_comm]
    _ ≤ ∑ v : M.Vertex, M.vertexDegree v := by
      apply Finset.sum_le_sum
      intro v _
      exact C.vertexDegree v
    _ = 2 * M.edgeCount := M.sum_vertexDegree_eq_two_mul_edgeCount

/-- The map-level hypotheses produce exactly the numerical data used by the
spherical curvature computation. -/
noncomputable def toCounts
    (C : TriangularSphericalMap minimumDegree M) :
    TriangularSphereCounts minimumDegree where
  vertexCount := M.vertexCount
  edgeCount := M.edgeCount
  faceCount := M.faceCount
  euler := C.euler_count
  faceIncidence := C.face_incidence
  vertexIncidence := C.vertex_incidence

/-- No triangular planar map can have all vertex degrees at least six. -/
theorem false_of_six_le
    (C : TriangularSphericalMap minimumDegree M)
    (hdegree : 6 ≤ minimumDegree) : False := by
  exact C.toCounts.false_of_six_le hdegree

/-- A reduced `C(3)`--`T(8)` spherical map is impossible. -/
theorem not_nonempty_eight (M : CombMap) :
    ¬ Nonempty (TriangularSphericalMap 8 M) := by
  rintro ⟨C⟩
  exact C.false_of_six_le (by norm_num)

/-- There is no closed combinatorial map satisfying the local spherical
conditions of a reduced `C(3)`--`T(8)` diagram. -/
theorem not_exists_eight :
    ¬ ∃ M : CombMap, Nonempty (TriangularSphericalMap 8 M) := by
  rintro ⟨M, C⟩
  exact not_nonempty_eight M C

end TriangularSphericalMap

/-! ## Local presentation data on a spherical map -/

section PresentationLink

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- The local information read from a reduced spherical diagram over a
literal triangular presentation.  Each face is assigned a defining triangle,
and the corners around each vertex form a periodic nonbacktracking walk in the
presentation link. -/
structure TriangularRelatorSphericalMap
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (M : CombMap) where
  /-- The underlying closed map is a combinatorial two-sphere. -/
  planar : M.IsPlanar
  /-- Every face is assigned a literal defining relator. -/
  faceRelator : ∀ f : M.Face, ∃ j : TriangleIndex,
    M.faceDegree f = (TriangularHodgeLayer.letters (T j)).length
  /-- Reduced corners around a vertex give a nonbacktracking link circuit. -/
  vertexLink : ∀ v : M.Vertex,
    KazhdanHyp.PresentationLinkWalk T (M.vertexDegree v)

namespace TriangularRelatorSphericalMap

variable {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
  {d : ℕ} {M : CombMap}

/-- Checked face lengths and presentation-link girth produce the local
degree data used by spherical curvature. -/
def toTriangularSphericalMap
    (C : TriangularRelatorSphericalMap T M)
    (hchecks : KazhdanHyp.GirthEightChecks T d) :
    TriangularSphericalMap 8 M where
  planar := C.planar
  faceDegree := by
    intro f
    obtain ⟨j, hj⟩ := C.faceRelator f
    simpa only [TriangularHodgeLayer.letters_eq_three, List.length_cons,
      List.length_nil, Nat.reduceAdd] using hj
  vertexDegree := by
    intro v
    exact (C.vertexLink v).eight_le_length hchecks

/-- A checked girth-eight table admits no reduced spherical diagram with the
literal face and vertex-link data above. -/
theorem false_of_girthEightChecks
    (C : TriangularRelatorSphericalMap T M)
    (hchecks : KazhdanHyp.GirthEightChecks T d) : False :=
  (C.toTriangularSphericalMap hchecks).false_of_six_le (by norm_num)

end TriangularRelatorSphericalMap

end PresentationLink

end VanKampen
end GGT

namespace KazhdanHyp

open PresentedGroupRelatorReplay

universe w

/-! ## From spherical extraction to finite-order localization -/

section CheckedTable

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- The reduced-sphere extraction step and spherical curvature give the
finite-order relator localization needed for torsion-freeness.

The extraction premise is the geometric content still required from the
small-cancellation topology: a nonidentity element with a positive power
equal to one, together with the absence of proper-power relators, produces a
closed reduced spherical diagram.  Literal face relators and the reduced
corner walks are enough; `GirthEightChecks` derives degree eight, and spherical
curvature rules out the result. -/
theorem finiteOrderForcesRelatorProperPower_of_sphericalExtraction
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (hchecks : GirthEightChecks T d)
    (extract :
      ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ),
        0 < n → g ^ n = 1 → g ≠ 1 →
        (∀ j, ¬ RelatorIsProperPower
          (TriangularHodgeLayer.relator (T j))) →
        ∃ M : GGT.VanKampen.CombMap.{w},
          Nonempty (GGT.VanKampen.TriangularRelatorSphericalMap T M)) :
    FiniteOrderForcesRelatorProperPower T := by
  classical
  intro g n hn hpow hne
  by_contra hproper
  have hnoProper : ∀ j, ¬ RelatorIsProperPower
      (TriangularHodgeLayer.relator (T j)) := by
    intro j hj
    exact hproper ⟨j, hj⟩
  obtain ⟨M, ⟨C⟩⟩ := extract g n hn hpow hne hnoProper
  exact C.false_of_girthEightChecks hchecks

/-- For one checked triangle table, reduced-sphere extraction closes the
torsion-freeness proof.  The algebraic no-proper-power input is already proved
from positivity and `GirthEightChecks.noCube`. -/
theorem presented_isPowerTorsionFree_of_sphericalExtraction
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (hchecks : GirthEightChecks T d)
    (extract :
      ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ),
        0 < n → g ^ n = 1 → g ≠ 1 →
        (∀ j, ¬ RelatorIsProperPower
          (TriangularHodgeLayer.relator (T j))) →
        ∃ M : GGT.VanKampen.CombMap.{w},
          Nonempty (GGT.VanKampen.TriangularRelatorSphericalMap T M)) :
    IsPowerTorsionFree (TriangularHodgeLayer.Presented T) := by
  have hloc : FiniteOrderForcesRelatorProperPower T :=
    finiteOrderForcesRelatorProperPower_of_sphericalExtraction hchecks extract
  exact presented_isPowerTorsionFree_of_finiteOrderForcesRelatorProperPower
    hchecks hloc

end CheckedTable

end KazhdanHyp
end GroupApproximation
