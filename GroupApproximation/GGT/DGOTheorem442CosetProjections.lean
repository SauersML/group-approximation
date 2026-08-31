import GroupApproximation.GGT.DGOTheorem442ProjectionDiameter

/-!
# DGO Theorem 4.42: equivariant projections between coset orbits

The vertices in DGO's projection complex are the orbits of left cosets `gH`.
This file makes the change of coordinates used throughout that construction
literal.  Left multiplication carries the orbit of `gH` onto the orbit of
`agH`; consequently approximate nearest-point projections exist on every
coset orbit, are equivariant, and have the same uniform diameter bound as
projections to the subgroup orbit itself.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

omit [PseudoMetricSpace S] in
/-- The orbit of the identity left coset is the subgroup orbit. -/
theorem leftCosetOrbitAt_one (H : Subgroup G) (s : S) :
    leftCosetOrbitAt H 1 s = subgroupOrbitAt H s := by
  ext x
  constructor
  · rintro ⟨h, hh, hxs⟩
    exact ⟨h, hh, by simpa using hxs⟩
  · rintro ⟨h, hh, hxs⟩
    exact ⟨h, hh, by simpa using hxs⟩

omit [PseudoMetricSpace S] in
/-- Left multiplication carries one coset orbit exactly to the corresponding
translated coset orbit. -/
theorem image_smul_leftCosetOrbitAt
    (H : Subgroup G) (s : S) (a g : G) :
    (fun z : S => a • z) '' leftCosetOrbitAt H g s =
      leftCosetOrbitAt H (a * g) s := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (smul_mem_leftCosetOrbitAt_iff H s a g x).mp hx
  · intro hz
    refine ⟨a⁻¹ • z, ?_, by simp⟩
    apply (smul_mem_leftCosetOrbitAt_iff H s a g (a⁻¹ • z)).mpr
    simpa using hz

omit [PseudoMetricSpace S] in
/-- Translating a `gH`-orbit back by `g⁻¹` gives the subgroup orbit. -/
theorem image_inv_smul_leftCosetOrbitAt
    (H : Subgroup G) (s : S) (g : G) :
    (fun z : S => g⁻¹ • z) '' leftCosetOrbitAt H g s =
      subgroupOrbitAt H s := by
  rw [image_smul_leftCosetOrbitAt, inv_mul_cancel, leftCosetOrbitAt_one]

omit [PseudoMetricSpace S] in
/-- Representatives of the same left coset define the same orbit subset. -/
theorem leftCosetOrbitAt_eq_of_inv_mul_mem
    (H : Subgroup G) (s : S) {f g : G} (hfg : f⁻¹ * g ∈ H) :
    leftCosetOrbitAt H f s = leftCosetOrbitAt H g s := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(f⁻¹ * g)⁻¹ * a, H.mul_mem (H.inv_mem hfg) ha, ?_⟩
    congr 1
    group
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(f⁻¹ * g) * a, H.mul_mem hfg ha, ?_⟩
    congr 1
    group

/-- For an unbounded geometrically separated orbit, equality of orbit subsets
is exactly equality of the corresponding left cosets. -/
theorem leftCosetOrbitAt_eq_iff_inv_mul_mem
    (H : Subgroup G) (s : S) (f g : G)
    (hsep : GeometricallySeparatedAt H s)
    (hunbounded : ∀ R : ℝ, ∃ h : G, h ∈ H ∧ R ≤ dist s (h • s)) :
    leftCosetOrbitAt H f s = leftCosetOrbitAt H g s ↔ f⁻¹ * g ∈ H :=
  ⟨fun horbit ↦ inv_mul_mem_of_leftCosetOrbitAt_eq H s f g hsep hunbounded horbit,
    leftCosetOrbitAt_eq_of_inv_mul_mem H s⟩

omit [PseudoMetricSpace S] in
/-- The orbit subset attached to a left coset, independent of its
representative.  This is DGO's actual projection-complex vertex map. -/
def cosetOrbitAt (H : Subgroup G) (s : S) (q : G ⧸ H) : Set S :=
  Quotient.liftOn' q (fun g ↦ leftCosetOrbitAt H g s) (by
    intro f g hfg
    exact leftCosetOrbitAt_eq_of_inv_mul_mem H s
      (QuotientGroup.leftRel_apply.mp hfg))

omit [PseudoMetricSpace S] in
@[simp] theorem cosetOrbitAt_mk (H : Subgroup G) (s : S) (g : G) :
    cosetOrbitAt H s (QuotientGroup.mk g) = leftCosetOrbitAt H g s :=
  rfl

/-- Under unbounded geometric separation, the coset-orbit vertex map is
injective.  Thus no distinct projection-complex vertices are accidentally
identified by a nonfaithful action on the ambient space. -/
theorem cosetOrbitAt_injective
    (H : Subgroup G) (s : S)
    (hsep : GeometricallySeparatedAt H s)
    (hunbounded : ∀ R : ℝ, ∃ h : G, h ∈ H ∧ R ≤ dist s (h • s)) :
    Function.Injective (cosetOrbitAt H s) := by
  intro x y hxy
  obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [cosetOrbitAt_mk, cosetOrbitAt_mk] at hxy
  exact QuotientGroup.eq.mpr
    ((leftCosetOrbitAt_eq_iff_inv_mul_mem H s f g hsep hunbounded).mp hxy)

omit [PseudoMetricSpace S] in
/-- The coset-orbit vertex map intertwines the natural left action on cosets
with pointwise translation of orbit subsets. -/
theorem cosetOrbitAt_smul (H : Subgroup G) (s : S) (a : G) (q : G ⧸ H) :
    cosetOrbitAt H s (a • q) = (fun z : S ↦ a • z) '' cosetOrbitAt H s q := by
  induction q using QuotientGroup.induction_on with
  | _ g =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, cosetOrbitAt_mk,
        cosetOrbitAt_mk, image_smul_leftCosetOrbitAt]

/-- A positive-error approximate projection to a left-coset orbit. -/
def IsApproxLeftCosetProjectionAt (H : Subgroup G) (s : S)
    (g : G) (a x : S) (κ : ℝ) : Prop :=
  IsApproxProjectionTo (leftCosetOrbitAt H g s) a x κ

omit [PseudoMetricSpace S] in
/-- Every coset orbit is nonempty. -/
theorem leftCosetOrbitAt_nonempty (H : Subgroup G) (s : S) (g : G) :
    (leftCosetOrbitAt H g s).Nonempty :=
  ⟨g • s, 1, H.one_mem, by simp⟩

/-- Positive-error approximate projections exist on every coset orbit. -/
theorem exists_isApproxLeftCosetProjectionAt
    (H : Subgroup G) (s : S) (g : G) (a : S)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ x : S, IsApproxLeftCosetProjectionAt H s g a x κ :=
  exists_isApproxProjectionTo (leftCosetOrbitAt H g s) a
    (leftCosetOrbitAt_nonempty H s g) hκ

/-- Approximate coset-orbit projections are equivariant under left
multiplication. -/
theorem isApproxLeftCosetProjectionAt_smul
    (hiso : IsIsometricAction G S) (a g : G) {p x : S} {κ : ℝ}
    (h : IsApproxLeftCosetProjectionAt H s g p x κ) :
    IsApproxLeftCosetProjectionAt H s (a * g) (a • p) (a • x) κ := by
  unfold IsApproxLeftCosetProjectionAt at h ⊢
  simpa only [image_smul_leftCosetOrbitAt] using
    isApproxProjectionTo_smul hiso a (leftCosetOrbitAt H g s) h

/-- The uniform subgroup-orbit projection-diameter estimate transports to
every left-coset orbit. -/
theorem dist_approxLeftCosetProjection_le
    {δ σ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s a x y : S} {g : G}
    (hquasi : ∀ (p q : G), p ∈ H → q ∈ H →
      ∀ f : ℝ → S, IsGeodesicSegment f 0 (dist (p • s) (q • s)) →
        f 0 = p • s → f (dist (p • s) (q • s)) = q • s →
          ∀ t ∈ Set.Icc (0 : ℝ) (dist (p • s) (q • s)),
            ∃ c : G, c ∈ H ∧ dist (f t) (c • s) ≤ σ)
    (hx : IsApproxLeftCosetProjectionAt H s g a x δ)
    (hy : IsApproxLeftCosetProjectionAt H s g a y δ) :
    dist x y ≤ 14 * δ + 2 * σ := by
  have hx' := isApproxProjectionTo_smul hiso g⁻¹
    (leftCosetOrbitAt H g s) hx
  have hy' := isApproxProjectionTo_smul hiso g⁻¹
    (leftCosetOrbitAt H g s) hy
  rw [image_inv_smul_leftCosetOrbitAt] at hx' hy'
  have hbound := dist_approxOrbitProjection_le hδ hδ0 hgeo hquasi hx' hy'
  rw [hiso g⁻¹ x y] at hbound
  exact hbound

/-- Quasiconvexity supplies one projection-diameter constant simultaneously
for every left coset. -/
theorem exists_approxLeftCosetProjection_diameter_bound
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    {H : Subgroup G} {s : S} (hqc : IsQuasiconvexOrbitAt H s) :
    ∃ ν : ℝ, 0 ≤ ν ∧ ∀ (g : G) (a x y : S),
      IsApproxLeftCosetProjectionAt H s g a x δ →
      IsApproxLeftCosetProjectionAt H s g a y δ → dist x y ≤ ν := by
  obtain ⟨σ, hσ0, hquasi⟩ := hqc
  refine ⟨14 * δ + 2 * σ, by positivity, ?_⟩
  intro g a x y hx hy
  exact dist_approxLeftCosetProjection_le hδ hδ0 hgeo hiso hquasi hx hy

end Elementary
end GGT
end GroupApproximation
