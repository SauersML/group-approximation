import GroupApproximation.GGT.DGOTheorem442ProjectionSeparation

/-!
# DGO Theorem 4.42: the first two projection axioms

Dahmani--Guirardel--Osin define

`d^π_Y(A,B) = diam(proj_Y(A) ∪ proj_Y(B))`.

Using a real-valued infimum at this stage would hide the only facts used in
axioms (A1) and (A2).  We instead record the equivalent upper-bound relation:
every pair of points in the displayed union is at distance at most `r`.
Symmetry is then literal, and the triangle inequality follows by choosing one
approximate projection of the middle orbit.  Approximate projections are
nonempty for every positive error, so no nearest-point existence assumption is
being smuggled into the argument.

The last theorem proves equivariance of the bound under the group action.  This
is the precise fact used later to make the action on the projection complex
isometric.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- `r` is an upper bound for DGO's projection distance
`d^π_Y(A,B)`: every two points in
`proj_Y(A) ∪ proj_Y(B)` are at distance at most `r`. -/
def ApproxCosetProjectionPairDiameterLE
    (H : Subgroup G) (s : S) (κ : ℝ)
    (Y A B : G ⧸ H) (r : ℝ) : Prop :=
  ∀ x : S,
    (x ∈ approxCosetProjectionSet H s κ Y A ∨
      x ∈ approxCosetProjectionSet H s κ Y B) →
    ∀ y : S,
      (y ∈ approxCosetProjectionSet H s κ Y A ∨
        y ∈ approxCosetProjectionSet H s κ Y B) →
      dist x y ≤ r

/-- **Projection axiom (A1), in upper-bound form.**  Interchanging the two
source vertices does not change the union whose diameter is being bounded. -/
theorem approxCosetProjectionPairDiameterLE_comm
    (H : Subgroup G) (s : S) (κ : ℝ) (Y A B : G ⧸ H) (r : ℝ) :
    ApproxCosetProjectionPairDiameterLE H s κ Y A B r ↔
      ApproxCosetProjectionPairDiameterLE H s κ Y B A r := by
  constructor <;> intro h x hx y hy
  · exact h x (hx.elim Or.inr Or.inl) y (hy.elim Or.inr Or.inl)
  · exact h x (hx.elim Or.inr Or.inl) y (hy.elim Or.inr Or.inl)

/-- **Projection axiom (A2), in upper-bound form.**  If `r` bounds
`d^π_Y(A,B)` and `t` bounds `d^π_Y(B,C)`, then `r+t` bounds
`d^π_Y(A,C)`.

The proof chooses a single point in `proj_Y(B)`.  Its existence follows from
positive-error approximate projection, and the four membership cases are the
ordinary metric triangle inequality. -/
theorem approxCosetProjectionPairDiameterLE_triangle
    (H : Subgroup G) (s : S) {κ : ℝ} (hκ : 0 < κ)
    (Y A B C : G ⧸ H) {r t : ℝ}
    (hAB : ApproxCosetProjectionPairDiameterLE H s κ Y A B r)
    (hBC : ApproxCosetProjectionPairDiameterLE H s κ Y B C t) :
    ApproxCosetProjectionPairDiameterLE H s κ Y A C (r + t) := by
  obtain ⟨z, hz⟩ := approxCosetProjectionSet_nonempty H s
    (Y := Y) (Z := B) hκ
  intro x hx y hy
  rcases hx with hxA | hxC
  · rcases hy with hyA | hyC
    · have ht0 : 0 ≤ t := by
        have hzz := hBC z (Or.inl hz) z (Or.inl hz)
        simpa using hzz
      exact le_trans (hAB x (Or.inl hxA) y (Or.inl hyA))
        (le_add_of_nonneg_right ht0)
    · calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ ≤ r + t := add_le_add
          (hAB x (Or.inl hxA) z (Or.inr hz))
          (hBC z (Or.inl hz) y (Or.inr hyC))
  · rcases hy with hyA | hyC
    · calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ ≤ t + r := add_le_add
          (hBC x (Or.inr hxC) z (Or.inl hz))
          (hAB z (Or.inr hz) y (Or.inl hyA))
        _ = r + t := add_comm t r
    · have hr0 : 0 ≤ r := by
        have hzz := hAB z (Or.inr hz) z (Or.inr hz)
        simpa using hzz
      exact le_trans (hBC x (Or.inr hxC) y (Or.inr hyC))
        (le_add_of_nonneg_left hr0)

/-- For distinct source vertices, the union defining DGO's projection
distance has a finite real upper bound.

Lemma 4.46 bounds each of the two projection sets by the same constant `ν`.
Choosing one point in each set then bounds a mixed pair by the distance
between the chosen points plus `2 * ν`. -/
theorem exists_approxCosetProjectionPairDiameterLE
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S} (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s)
    (Y A B : G ⧸ H) (hYA : Y ≠ A) (hYB : Y ≠ B) :
    ∃ r : ℝ, ApproxCosetProjectionPairDiameterLE H s δ Y A B r := by
  obtain ⟨ν, hν0, hν⟩ :=
    exists_approxCosetProjectionSet_diameter_bound
      hδ hδ0 hgeo hiso hqc hsep
  obtain ⟨a, ha⟩ := approxCosetProjectionSet_nonempty H s
    (Y := Y) (Z := A) hδpos
  obtain ⟨b, hb⟩ := approxCosetProjectionSet_nonempty H s
    (Y := Y) (Z := B) hδpos
  refine ⟨2 * ν + dist a b, ?_⟩
  intro x hx y hy
  rcases hx with hxA | hxB
  · rcases hy with hyA | hyB
    · have hxy : dist x y ≤ ν := hν Y A hYA x hxA y hyA
      have hdab : 0 ≤ dist a b := dist_nonneg
      linarith
    · have hxa : dist x a ≤ ν := hν Y A hYA x hxA a ha
      have hby : dist b y ≤ ν := hν Y B hYB b hb y hyB
      calc
        dist x y ≤ dist x a + dist a b + dist b y := dist_triangle4 x a b y
        _ ≤ ν + dist a b + ν := by gcongr
        _ = 2 * ν + dist a b := by ring
  · rcases hy with hyA | hyB
    · have hxb : dist x b ≤ ν := hν Y B hYB x hxB b hb
      have hay : dist a y ≤ ν := hν Y A hYA a ha y hyA
      calc
        dist x y ≤ dist x b + dist b a + dist a y := dist_triangle4 x b a y
        _ ≤ ν + dist b a + ν := by gcongr
        _ = 2 * ν + dist a b := by rw [dist_comm b a]; ring
    · have hxy : dist x y ≤ ν := hν Y B hYB x hxB y hyB
      have hdab : 0 ≤ dist a b := dist_nonneg
      linarith

/-- The union of the two approximate projection sets occurring in DGO's
definition of `d^π_Y(A,B)`. -/
def approxCosetProjectionPairSet
    (H : Subgroup G) (s : S) (κ : ℝ) (Y A B : G ⧸ H) : Set S :=
  approxCosetProjectionSet H s κ Y A ∪
    approxCosetProjectionSet H s κ Y B

/-- For three distinct projection-complex vertices, the set whose diameter
defines `d^π_Y(A,B)` is bounded. -/
theorem approxCosetProjectionPairSet_isBounded
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S} (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s)
    (Y A B : G ⧸ H) (hYA : Y ≠ A) (hYB : Y ≠ B) :
    Bornology.IsBounded (approxCosetProjectionPairSet H s δ Y A B) := by
  obtain ⟨r, hr⟩ := exists_approxCosetProjectionPairDiameterLE
    hδ hδ0 hδpos hgeo hiso hqc hsep Y A B hYA hYB
  rw [Metric.isBounded_iff]
  refine ⟨r, ?_⟩
  intro x hx y hy
  exact hr x (by simpa [approxCosetProjectionPairSet] using hx)
    y (by simpa [approxCosetProjectionPairSet] using hy)

/-- DGO's approximate projection distance
`d^π_Y(A,B) = diam(proj_Y(A) ∪ proj_Y(B))`.

Mathlib's `Metric.diam` is `0` on an unbounded set, so this agrees with DGO's
diameter only where the pair set is bounded; the boundedness proved just above
(`approxCosetProjectionPairSet_isBounded`, DGO Lemma 4.46's
bound `ν`) is what the projection axioms below are stated under, and the
final Theorem 4.42 mentions no diameter at all. -/
noncomputable def approxCosetProjectionDistance
    (H : Subgroup G) (s : S) (κ : ℝ) (Y A B : G ⧸ H) : ℝ :=
  Metric.diam (approxCosetProjectionPairSet H s κ Y A B)

/-- **Projection axiom (A1).** -/
theorem approxCosetProjectionDistance_comm
    (H : Subgroup G) (s : S) (κ : ℝ) (Y A B : G ⧸ H) :
    approxCosetProjectionDistance H s κ Y A B =
      approxCosetProjectionDistance H s κ Y B A := by
  simp only [approxCosetProjectionDistance, approxCosetProjectionPairSet,
    Set.union_comm]

/-- **Projection axiom (A2).**  This is the triangle inequality for the
real-valued diameter, not merely for a chosen upper bound. -/
theorem approxCosetProjectionDistance_triangle
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S} (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s)
    (Y A B C : G ⧸ H) (hYA : Y ≠ A) (hYB : Y ≠ B) (hYC : Y ≠ C) :
    approxCosetProjectionDistance H s δ Y A C ≤
      approxCosetProjectionDistance H s δ Y A B +
        approxCosetProjectionDistance H s δ Y B C := by
  let UAB := approxCosetProjectionPairSet H s δ Y A B
  let UBC := approxCosetProjectionPairSet H s δ Y B C
  have hUAB : Bornology.IsBounded UAB :=
    approxCosetProjectionPairSet_isBounded hδ hδ0 hδpos hgeo hiso hqc hsep
      Y A B hYA hYB
  have hUBC : Bornology.IsBounded UBC :=
    approxCosetProjectionPairSet_isBounded hδ hδ0 hδpos hgeo hiso hqc hsep
      Y B C hYB hYC
  obtain ⟨z, hz⟩ := approxCosetProjectionSet_nonempty H s
    (Y := Y) (Z := B) hδpos
  apply Metric.diam_le_of_forall_dist_le
    (add_nonneg Metric.diam_nonneg Metric.diam_nonneg)
  intro x hx y hy
  change x ∈ approxCosetProjectionPairSet H s δ Y A C at hx
  change y ∈ approxCosetProjectionPairSet H s δ Y A C at hy
  change dist x y ≤ Metric.diam UAB + Metric.diam UBC
  rcases hx with hxA | hxC
  · rcases hy with hyA | hyC
    · have hxy : dist x y ≤ Metric.diam UAB :=
        Metric.dist_le_diam_of_mem hUAB (Or.inl hxA) (Or.inl hyA)
      exact hxy.trans (le_add_of_nonneg_right Metric.diam_nonneg)
    · calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ ≤ Metric.diam UAB + Metric.diam UBC := add_le_add
          (Metric.dist_le_diam_of_mem hUAB (Or.inl hxA) (Or.inr hz))
          (Metric.dist_le_diam_of_mem hUBC (Or.inl hz) (Or.inr hyC))
  · rcases hy with hyA | hyC
    · calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ ≤ Metric.diam UBC + Metric.diam UAB := add_le_add
          (Metric.dist_le_diam_of_mem hUBC (Or.inr hxC) (Or.inl hz))
          (Metric.dist_le_diam_of_mem hUAB (Or.inr hz) (Or.inl hyA))
        _ = Metric.diam UAB + Metric.diam UBC := add_comm _ _
    · have hxy : dist x y ≤ Metric.diam UBC :=
        Metric.dist_le_diam_of_mem hUBC (Or.inr hxC) (Or.inr hyC)
      exact hxy.trans (le_add_of_nonneg_left Metric.diam_nonneg)

/-- The set defining the projection distance is carried exactly to the
translated projection set. -/
theorem approxCosetProjectionPairSet_smul
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (g : G) (κ : ℝ) (Y A B : G ⧸ H) :
    approxCosetProjectionPairSet H s κ (g • Y) (g • A) (g • B) =
      (fun x : S ↦ g • x) '' approxCosetProjectionPairSet H s κ Y A B := by
  simp only [approxCosetProjectionPairSet,
    approxCosetProjectionSet_smul hiso, Set.image_union]

/-- Simultaneous left translation preserves DGO's real-valued projection
distance. -/
theorem approxCosetProjectionDistance_smul
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (g : G) (κ : ℝ) (Y A B : G ⧸ H) :
    approxCosetProjectionDistance H s κ (g • Y) (g • A) (g • B) =
      approxCosetProjectionDistance H s κ Y A B := by
  rw [approxCosetProjectionDistance, approxCosetProjectionPairSet_smul hiso]
  exact (Isometry.of_dist_eq (hiso g)).diam_image _

/-- Projection-diameter upper bounds are exactly equivariant under left
translation of all three coset vertices. -/
theorem approxCosetProjectionPairDiameterLE_smul_iff
    (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (g : G) (κ : ℝ)
    (Y A B : G ⧸ H) (r : ℝ) :
    ApproxCosetProjectionPairDiameterLE H s κ (g • Y) (g • A) (g • B) r ↔
      ApproxCosetProjectionPairDiameterLE H s κ Y A B r := by
  constructor
  · intro h x hx y hy
    have hx' : g • x ∈ approxCosetProjectionSet H s κ (g • Y) (g • A) ∨
        g • x ∈ approxCosetProjectionSet H s κ (g • Y) (g • B) := by
      rcases hx with hx | hx
      · exact Or.inl (by
          rw [approxCosetProjectionSet_smul hiso H s g κ Y A]
          exact ⟨x, hx, rfl⟩)
      · exact Or.inr (by
          rw [approxCosetProjectionSet_smul hiso H s g κ Y B]
          exact ⟨x, hx, rfl⟩)
    have hy' : g • y ∈ approxCosetProjectionSet H s κ (g • Y) (g • A) ∨
        g • y ∈ approxCosetProjectionSet H s κ (g • Y) (g • B) := by
      rcases hy with hy | hy
      · exact Or.inl (by
          rw [approxCosetProjectionSet_smul hiso H s g κ Y A]
          exact ⟨y, hy, rfl⟩)
      · exact Or.inr (by
          rw [approxCosetProjectionSet_smul hiso H s g κ Y B]
          exact ⟨y, hy, rfl⟩)
    calc
      dist x y = dist (g • x) (g • y) := (hiso g x y).symm
      _ ≤ r := h (g • x) hx' (g • y) hy'
  · intro h x hx y hy
    have pullback_mem {Z : G ⧸ H} {w : S}
        (hw : w ∈ approxCosetProjectionSet H s κ (g • Y) (g • Z)) :
        g⁻¹ • w ∈ approxCosetProjectionSet H s κ Y Z := by
      rw [approxCosetProjectionSet_smul hiso H s g κ Y Z] at hw
      obtain ⟨w₀, hw₀, rfl⟩ := hw
      simpa using hw₀
    have hx' : g⁻¹ • x ∈ approxCosetProjectionSet H s κ Y A ∨
        g⁻¹ • x ∈ approxCosetProjectionSet H s κ Y B :=
      hx.elim (fun hxA => Or.inl (pullback_mem hxA))
        (fun hxB => Or.inr (pullback_mem hxB))
    have hy' : g⁻¹ • y ∈ approxCosetProjectionSet H s κ Y A ∨
        g⁻¹ • y ∈ approxCosetProjectionSet H s κ Y B :=
      hy.elim (fun hyA => Or.inl (pullback_mem hyA))
        (fun hyB => Or.inr (pullback_mem hyB))
    have hxy := h (g⁻¹ • x) hx' (g⁻¹ • y) hy'
    calc
      dist x y = dist (g⁻¹ • x) (g⁻¹ • y) := (hiso g⁻¹ x y).symm
      _ ≤ r := hxy

end Elementary
end GGT
end GroupApproximation
