import GroupApproximation.GGT.HullSCRelatorSeparation2Filling
import GroupApproximation.GGT.HullSCFilling

/-!
# The rotating data Hull's Theorem 5.1 consumes, in the form DGO's theorem is
provable in

`HullSC.RotatingData` records the geometry Hull's §5 produces and DGO's Theorem
5.3 consumes.  Two clauses of it are in motion, for a reason recorded in
`GGT/HullSCDGO.lean`: `HullSC.DGOQuotientStatement` as transcribed is **false**
-- with no geodesic the very rotating condition constrains an annulus that can
be empty -- and `HullSC.DGOQuotientStatementGeodesic` is the repair.  A record
that is to be fed to the repaired statement has to carry `IsGeodesicSpace`.

`RotatingDataGeo₂` is that record, and it is stated here rather than reused so
that this lane rests on the geodesic statement without waiting on, or colliding
with, the corresponding repair of `RotatingData` itself.  It differs from
`HullSC.RotatingData` in three places, all of them the same correction:

* `isGeodesic` is present;
* the injectivity radius is a named field `injRadius` with `L < injRadius`,
  rather than the separation doing double duty;
* the metric clause is `kernel_moves_base`, quantified over the subgroup the
  rotations generate and stated at the basepoint, rather than
  `injOn_of_dist`, which quantifies over quotient maps.

The last of these is a strengthening in form only: `injOn_cayleyBall` below
derives what the consumer actually needs -- injectivity of a quotient map on a
ball of `Γ(G,A)` -- in three lines, and the derivation is the only place a
quotient map is mentioned.  Everything else is `HullSC.RotatingData` verbatim.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- **The rotating data of Hull's Theorem 5.1, carrying a geodesic.**

`L` is the displacement below which the quotient has to be faithful; Hull's
proof prescribes it by taking the relator deep enough, which is why
`lt_injRadius` is a field rather than a hypothesis of the theorems below.

The space is taken in the same universe as `G`.  Over the manuscript's ground
universe that is no restriction: DGO's cone-off of `Γ(G,A)` along the cosets of
a hyperbolically embedded subgroup is built from `G` and `ℝ`, both of which are
there. -/
structure RotatingDataGeo₂ {G : Type u} [Group G] (A : Alphabet G) (w : G)
    (L : ℝ) where
  /-- DGO's cone-off. -/
  Space : Type u
  /-- Its metric. -/
  [metric : PseudoMetricSpace Space]
  /-- The action of `G` on it. -/
  [action : MulAction G Space]
  /-- The basepoint, the image of the identity vertex of `Γ(G,A)`. -/
  base : Space
  /-- Every letter of `A` moves the basepoint by at most one: `Γ(G,A)` sits in
  the cone-off with its edges of length one. -/
  letter_dist : ∀ a ∈ A.carrier, dist base (a • base) ≤ 1
  /-- The hyperbolicity constant of the cone-off. -/
  delta : ℝ
  /-- It is positive. -/
  delta_pos : 0 < delta
  /-- The cone-off is hyperbolic. -/
  hyperbolic : IsHyperbolicSpace delta Space
  /-- **The cone-off is geodesic**, which is what
  `HullSC.DGOQuotientStatementGeodesic` asks for. -/
  isGeodesic : IsGeodesicSpace Space
  /-- The separation of the family. -/
  sep : ℝ
  /-- DGO's Theorem 5.3 asks for separation above `200 δ`. -/
  sep_ge : 200 * delta ≤ sep
  /-- The apices: one cone point over each coset carrying a rotation. -/
  apices : Set Space
  /-- The rotation subgroups. -/
  rot : Space → Subgroup G
  /-- They form a rotating family. -/
  isRotatingFamily : IsRotatingFamily G Space apices rot
  /-- It is `sep`-separated. -/
  isSeparated : IsSeparated apices sep
  /-- It is very rotating. -/
  isVeryRotating : IsVeryRotating G Space delta apices rot
  /-- The rotations generate the normal closure of the relator: killing the
  family is killing `w`. -/
  rotationNormalClosure_eq :
    rotationNormalClosure apices rot = Subgroup.normalClosure ({w} : Set G)
  /-- The injectivity radius. -/
  injRadius : ℝ
  /-- It exceeds the prescribed displacement. -/
  lt_injRadius : L < injRadius
  /-- **The kernel moves the basepoint**, and this is Hull's §5 rather than
  DGO's: Theorem 5.3 concludes the free splitting and the dichotomy, and an
  injectivity radius follows from neither, loxodromy being asymptotic and the
  splitting not metric.  It is stated at the basepoint because
  `HullSC.eq_one_of_dist_lt_everywhere` refutes the form quantified over every
  point: a rotation fixes its apex and lies in the kernel. -/
  kernel_moves_base : ∀ g ∈ rotationNormalClosure apices rot, g ≠ 1 →
    injRadius ≤ dist base (g • base)

namespace RotatingDataGeo₂

instance instMetric {G : Type u} [Group G] {A : Alphabet G} {w : G} {L : ℝ}
    (D : RotatingDataGeo₂ A w L) : PseudoMetricSpace D.Space := D.metric

instance instAction {G : Type u} [Group G] {A : Alphabet G} {w : G} {L : ℝ}
    (D : RotatingDataGeo₂ A w L) : MulAction G D.Space := D.action

/-- The action on the cone-off is by isometries: it is a field of the rotating
family. -/
theorem isometric {G : Type u} [Group G] {A : Alphabet G} {w : G} {L : ℝ}
    (D : RotatingDataGeo₂ A w L) : IsIsometricAction G D.Space :=
  D.isRotatingFamily.isometric

/-- **Injectivity of the quotient on the ball, from the injectivity radius.**

The only place a quotient map meets the geometry.  An element of the ball of
radius `R` sends a pair of points of `Γ(G,A)` to the same image only through an
element of length at most `2R`, which moves the basepoint by at most `2R` and
so by less than `injRadius`; if it were killed it would lie in the subgroup the
rotations generate, and `kernel_moves_base` forbids that. -/
theorem injOn_cayleyBall {G : Type u} [Group G] {A : Alphabet G} {w : G}
    {R : ℕ} (D : RotatingDataGeo₂ A w (2 * (R : ℝ))) {Q : Type v} [Group Q]
    (q : G →* Q) (hker : q.ker = Subgroup.normalClosure ({w} : Set G)) :
    Set.InjOn q (cayleyBall A R) := by
  refine injOn_cayleyBall_of_action D.isometric A D.base D.letter_dist q
    (L := D.injRadius) R D.lt_injRadius ?_
  intro g hg1 hdist hq
  have hmem : g ∈ rotationNormalClosure D.apices D.rot := by
    have hk : g ∈ q.ker := MonoidHom.mem_ker.mpr hq
    rwa [hker, ← D.rotationNormalClosure_eq] at hk
  exact absurd (D.kernel_moves_base g hmem hg1) (not_le.mpr hdist)

end RotatingDataGeo₂

end HullSC
end GroupApproximation
