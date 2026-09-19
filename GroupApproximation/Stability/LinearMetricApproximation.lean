import GroupApproximation.Algebra.MalcevLinear
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Stable approximation by finite-dimensional linear metric groups

This file isolates the formal argument common to stability results for
Schatten metrics and other bi-invariant metrics on matrix groups.  It does not
assume any theorem from that literature.

For a family of metric groups, an almost representation is a sequence of maps
whose multiplicative defects vanish pointwise.  The group is approximated by
the family if every nonidentity element is uniformly separated from the
identity in some such sequence.  It is stable if every almost representation
is pointwise close to genuine homomorphisms into the same targets.

If every target embeds in a finite-dimensional general linear group, a
finitely generated group which is both approximated and stable is residually
finite.  Stability supplies a genuine representation that detects a prescribed
element.  Its image is finitely generated, hence residually finite by the
formalized Mal'cev theorem, and a finite quotient of that image detects the
element.
-/

namespace GroupApproximation
namespace LinearMetricApproximation

universe u v w z

variable (I : Type u) (M : I → Type v)
variable [∀ i, Group (M i)] [∀ i, PseudoMetricSpace (M i)]

/-- A sequence of maps into a family of metric groups with pointwise
vanishing multiplicative defect. -/
structure AlmostRepresentation (G : Type w) [Group G] where
  index : ℕ → I
  map : ∀ n, G → M (index n)
  asymptoticallyMultiplicative :
    ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      dist (map n (g * h)) (map n g * map n h) < ε

/-- Restrict an almost representation to a strictly increasing sequence of
coordinates.  Strict monotonicity is used only to ensure that the selected
coordinates tend to infinity. -/
def AlmostRepresentation.reindex {G : Type w} [Group G]
    (A : AlmostRepresentation I M G) (r : ℕ → ℕ) (hr : StrictMono r) :
    AlmostRepresentation I M G where
  index n := A.index (r n)
  map n := A.map (r n)
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h ε hε
    exact ⟨N, fun n hn ↦ hN (r n) (hn.trans (hr.id_le n))⟩

variable {I M}

/-- Every nonidentity element survives with a fixed positive metric gap in
some almost representation by the family. -/
def IsApproximatedBy (G : Type w) [Group G] : Prop :=
  ∀ x : G, x ≠ 1 →
    ∃ (A : AlmostRepresentation I M G) (δ : ℝ),
      0 < δ ∧ ∀ n, δ ≤ dist (A.map n x) (A.map n 1)

/-- The one-sequence approximation condition used in the printed
finite-Schatten definition: the maps take the identity to the identity, and a
single almost representation has positive `limsup` displacement from the
target identity at every nonidentity element. -/
def IsLimsupApproximatedBy (G : Type w) [Group G] : Prop :=
  ∃ A : AlmostRepresentation I M G,
    (∀ n, A.map n 1 = 1) ∧
      ∀ x : G, x ≠ 1 →
        0 < Filter.limsup
          (fun n ↦ dist (A.map n x) 1) Filter.atTop

/-- Positive `limsup` separation along one sequence supplies, for each fixed
nonidentity element, a strictly increasing subsequence with a uniform positive
gap.  This is the exact bridge from the printed approximation condition to
`IsApproximatedBy`; no uniform subsequence in the group element is asserted. -/
theorem isApproximatedBy_of_limsupApproximatedBy
    {G : Type w} [Group G]
    (h : IsLimsupApproximatedBy (I := I) (M := M) G) :
    IsApproximatedBy (I := I) (M := M) G := by
  obtain ⟨A, hone, hA⟩ := h
  intro x hx
  let L := Filter.limsup
    (fun n ↦ dist (A.map n x) 1) Filter.atTop
  have hL : 0 < L := hA x hx
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n ↦ dist (A.map n x) 1) :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop fun n ↦ dist_nonneg
  have hfrequent : ∃ᶠ n in Filter.atTop,
      L / 2 < dist (A.map n x) 1 :=
    Filter.frequently_lt_of_lt_limsup hcob (by linarith)
  obtain ⟨r, hr, hgap⟩ := Filter.extraction_of_frequently_atTop hfrequent
  exact ⟨AlmostRepresentation.reindex (I := I) (M := M) A r hr,
    L / 2, by linarith, fun n ↦ by
      change L / 2 ≤ dist (A.map (r n) x) (A.map (r n) 1)
      rw [hone (r n)]
      exact (hgap n).le⟩

/-- Every almost representation is pointwise asymptotic to genuine
homomorphisms into the same targets. -/
def IsStableWithRespectTo (G : Type w) [Group G] : Prop :=
  ∀ A : AlmostRepresentation I M G,
    ∃ π : ∀ n, G →* M (A.index n),
      ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        dist (A.map n g) (π n g) < ε

/-- The range of a homomorphism from a finitely generated group is finitely
generated. -/
theorem range_fg {G : Type w} [Group G] [hfg : Group.FG G]
    {K : Type z} [Group K] (f : G →* K) : f.range.FG := by
  classical
  obtain ⟨S, hS⟩ : (⊤ : Subgroup G).FG := hfg.out
  refine ⟨S.image f, ?_⟩
  rw [MonoidHom.range_eq_map, ← hS, Finset.coe_image, MonoidHom.map_closure]

/-- **Stable linear-metric approximation implies residual finiteness.**

No invariance axiom for the metrics is needed for this implication.  The
metric is used only through the triangle inequality.  In applications the
  targets are finite-dimensional unitary or general linear groups equipped with
  a Schatten metric; their linear embeddings are the maps `linear`
below. -/
theorem residuallyFinite_of_approximated_of_stable
    {G : Type w} [Group G] [Group.FG G]
    (F : I → Type z) [∀ i, Field (F i)]
    (d : I → ℕ)
    (linear : ∀ i, M i →* Matrix.GeneralLinearGroup (Fin (d i)) (F i))
    (linear_injective : ∀ i, Function.Injective (linear i))
    (happrox : IsApproximatedBy (I := I) (M := M) G)
    (hstable : IsStableWithRespectTo (I := I) (M := M) G) :
    Group.ResiduallyFinite G := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro x hx
  obtain ⟨A, δ, hδ, hseparate⟩ := happrox x hx
  obtain ⟨π, hπ⟩ := hstable A
  obtain ⟨Nx, hNx⟩ := hπ x (δ / 3) (by linarith)
  obtain ⟨N1, hN1⟩ := hπ 1 (δ / 3) (by linarith)
  let n := max Nx N1
  have hclose_x : dist (A.map n x) (π n x) < δ / 3 :=
    hNx n (le_max_left _ _)
  have hclose_one : dist (A.map n 1) (π n 1) < δ / 3 :=
    hN1 n (le_max_right _ _)
  have hπx : π n x ≠ 1 := by
    intro heq
    have hleft : dist (A.map n x) (1 : M (A.index n)) < δ / 3 := by
      simpa [heq] using hclose_x
    have hright : dist (1 : M (A.index n)) (A.map n 1) < δ / 3 := by
      simpa [dist_comm] using hclose_one
    have htri := dist_triangle (A.map n x) (1 : M (A.index n)) (A.map n 1)
    have hgap := hseparate n
    linarith
  let ρ : G →* Matrix.GeneralLinearGroup (Fin (d (A.index n))) (F (A.index n)) :=
    (linear (A.index n)).comp (π n)
  have hρx : ρ x ≠ 1 := by
    intro h
    apply hπx
    apply linear_injective (A.index n)
    simpa [ρ] using h
  haveI : Group.ResiduallyFinite ρ.range :=
    MalcevLinear.residuallyFinite_of_fg ρ.range (range_fg ρ)
  let y : ρ.range := ρ.rangeRestrict x
  have hy : y ≠ 1 := by
    intro h
    apply hρx
    exact Subtype.ext_iff.mp h
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem y hy
  letI := N.isNormal'
  letI := N.isFiniteIndex'
  refine ⟨ρ.range ⧸ N.toSubgroup, inferInstance, inferInstance,
    (QuotientGroup.mk' N.toSubgroup).comp ρ.rangeRestrict, ?_⟩
  intro h
  apply hN
  exact (QuotientGroup.eq_one_iff y).mp (by simpa [y] using h)

/-- The residual-finiteness implication with the printed one-sequence,
positive-`limsup` approximation hypothesis. -/
theorem residuallyFinite_of_limsupApproximated_of_stable
    {G : Type w} [Group G] [Group.FG G]
    (F : I → Type z) [∀ i, Field (F i)]
    (d : I → ℕ)
    (linear : ∀ i, M i →* Matrix.GeneralLinearGroup (Fin (d i)) (F i))
    (linear_injective : ∀ i, Function.Injective (linear i))
    (happrox : IsLimsupApproximatedBy (I := I) (M := M) G)
    (hstable : IsStableWithRespectTo (I := I) (M := M) G) :
    Group.ResiduallyFinite G :=
  residuallyFinite_of_approximated_of_stable F d linear linear_injective
    (isApproximatedBy_of_limsupApproximatedBy happrox) hstable

/-! ## Closed audit carriers -/

/-- The subsequence bridge with all of its mathematical parameters quantified
inside one closed proposition. -/
def LimsupSubsequencePrinciple : Prop :=
  ∀ (I : Type u) (M : I → Type v)
    [∀ i, Group (M i)] [∀ i, PseudoMetricSpace (M i)]
    (G : Type w) [Group G],
    IsLimsupApproximatedBy (I := I) (M := M) G →
      IsApproximatedBy (I := I) (M := M) G

theorem limsupSubsequencePrinciple : LimsupSubsequencePrinciple := by
  intro I M _ _ G _ h
  exact isApproximatedBy_of_limsupApproximatedBy h

/-- The stable-linear residual-finiteness argument, again with every parameter
inside the advertised proposition rather than supplied to its proof. -/
def LimsupStableLinearPrinciple : Prop :=
  ∀ (I : Type u) (M : I → Type v)
    [∀ i, Group (M i)] [∀ i, PseudoMetricSpace (M i)]
    (G : Type w) [Group G] [Group.FG G]
    (F : I → Type z) [∀ i, Field (F i)]
    (d : I → ℕ)
    (linear : ∀ i, M i →* Matrix.GeneralLinearGroup (Fin (d i)) (F i))
    (_linear_injective : ∀ i, Function.Injective (linear i)),
    IsLimsupApproximatedBy (I := I) (M := M) G →
      IsStableWithRespectTo (I := I) (M := M) G →
      Group.ResiduallyFinite G

theorem limsupStableLinearPrinciple : LimsupStableLinearPrinciple := by
  intro I M _ _ G _ _ F _ d linear linear_injective happrox hstable
  exact residuallyFinite_of_limsupApproximated_of_stable
    F d linear linear_injective happrox hstable

#audit_closed_axioms limsupSubsequencePrinciple
#audit_closed_axioms limsupStableLinearPrinciple

end LinearMetricApproximation
end GroupApproximation
