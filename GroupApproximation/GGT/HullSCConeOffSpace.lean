import GroupApproximation.GGT.HullSCFilling

/-!
# The rotating family of a cone-off, from one apex and one subgroup

**Superseded, and not merely unused.**  `Manuscript.NonMF.TheoremCAssembly` records
Hull's §5 over a **family** (`HullSC.HullConeOffStatement₂`, in
`GGT/HullSCRelatorSeparation2Quotient.lean`, with `HullSC.ConeOffData₂` for its
geometry), because the single-subgroup form below cannot carry Hull's relator:
over one `H` all of the relator's `H`-letters lie in one component of
`Γ(G, X ⊔ H)`, so the word is not quasi-geodesic
(`HullSC.not_quasiGeodesic_relatorWord`), which §5 requires it to be.  The
family form is the same construction with the index type freed --- nothing in
`apexRot`, `isRotatingFamily_apexRot` or `rotationNormalClosure_apexRot` depended
on it being `Unit`, which is why `apexRotFamily` and its three theorems read the
same.  Nothing on the trust surface consumes what is below.

Dahmani-Guirardel-Osin, *Hyperbolically embedded subgroups and rotating families
in groups acting on hyperbolic spaces*, Mem. Amer. Math. Soc. 245 (2017), §5.1,
after F. Dahmani and R. Coulon: the family a small cancellation quotient runs
over is not an arbitrary rotating family.  It has **one orbit of apices** and
**one rotation subgroup up to conjugacy**: the apices are the cone points over
the conjugates of the axis of the relator, so `G` permutes them transitively,
and the rotation subgroup at the cone point of `g` is `g K g⁻¹` with
`K = ⟨w⟩` the cyclic group on the relator.

`HullSC.RotatingData` asks for the equivariant assignment `Rot : X → Subgroup G`
and for the identification of the subgroup its rotations generate.  Neither is
geometry, and neither is proved anywhere below: both are consequences of the
apex and the subgroup.  This module proves them.

## What is discharged

* `apexRot` -- the assignment, defined at every point of the space: at a point
  of the orbit it is the conjugate `g K g⁻¹`, and away from the orbit it is
  trivial.  It is a subgroup because `K` is normal in the stabiliser of the
  apex, which is the one hypothesis the construction has to carry (and does
  carry: over a torsion-free ambient group the stabiliser of the cone point of
  `⟨w⟩` is the cyclic elementary closure, in which `⟨w⟩` is normal).
* `isRotatingFamily_apexRot` -- the three axioms of a rotating family.  The
  fixing axiom is that `K` fixes the apex; equivariance is automatic, the
  assignment being a union over all `g` carrying the apex to the point.
* `rotationNormalClosure_apexRot` -- the rotations generate the normal closure
  of `K`, so with `normalClosure_zpowers` the kernel clause of `RotatingData`
  is `⟨⟨w⟩⟩` on the nose.
* `isSeparated_apexOrbit`, `isVeryRotating_apexRot` -- the two geometric axioms,
  restated over the orbit and the conjugates, which is the form the cone-off
  construction produces them in.

## What is left

`ConeOffData` is what remains to be built: a hyperbolic geodesic `G`-space with
an apex whose orbit is separated, on which the conjugates of `K` are very
rotating, and in which the letters of `A` move the basepoint by at most one.
That is DGO's §5.1 cone-off with Coulon's hyperbolicity estimate, and it is the
whole of the geometry -- together with the two clauses that are Hull's own
rather than DGO's, the injectivity radius and the lifting of finite order, which
the structure carries for the reasons its fields record.
`hullFillingDataStatement_of_coneOff` is the reduction:
`HullFillingDataStatement` follows from `HullConeOffStatement`, whose first
conjunct asks for that space with `K = ⟨w⟩`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## The orbit of an apex, and the rotations over it -/

/-- The orbit of the apex: the set of apices. -/
def apexOrbit {G : Type u} [Group G] {X : Type v} [MulAction G X] (c₀ : X) :
    Set X :=
  {x | ∃ g : G, g • c₀ = x}

theorem mem_apexOrbit {G : Type u} [Group G] {X : Type v} [MulAction G X]
    {c₀ x : X} : x ∈ apexOrbit (G := G) c₀ ↔ ∃ g : G, g • c₀ = x := Iff.rfl

theorem self_mem_apexOrbit {G : Type u} [Group G] {X : Type v} [MulAction G X]
    (c₀ : X) : c₀ ∈ apexOrbit (G := G) c₀ :=
  ⟨1, one_smul G c₀⟩

/-- **The rotation subgroup at a point.**  At a point `g • c₀` of the orbit it
is the conjugate `g K g⁻¹`; away from the orbit it is trivial.

Taking the union over every `g` carrying the apex to the point, rather than a
chosen one, is what makes the definition well posed without a choice; that the
union is a subgroup is where `hnorm` -- `K` normal in the stabiliser -- is
spent, and it is spent nowhere else. -/
def apexRot {G : Type u} [Group G] {X : Type v} [MulAction G X]
    (K : Subgroup G) (c₀ : X)
    (hnorm : ∀ s : G, s • c₀ = c₀ → ∀ k ∈ K, s * k * s⁻¹ ∈ K) (x : X) :
    Subgroup G where
  carrier := {h : G | (∃ g : G, g • c₀ = x ∧ ∃ k ∈ K, h = g * k * g⁻¹) ∨ h = 1}
  one_mem' := Or.inr rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨g, hg, k, hk, rfl⟩ | rfl
    · rcases hb with ⟨g', hg', k', hk', rfl⟩ | rfl
      · have hs : (g⁻¹ * g') • c₀ = c₀ := by
          rw [mul_smul, hg', ← hg, ← mul_smul, inv_mul_cancel, one_smul]
        have hk2 : (g⁻¹ * g') * k' * (g⁻¹ * g')⁻¹ ∈ K := hnorm _ hs k' hk'
        refine Or.inl ⟨g, hg, k * ((g⁻¹ * g') * k' * (g⁻¹ * g')⁻¹),
          mul_mem hk hk2, ?_⟩
        group
      · rw [mul_one]
        exact Or.inl ⟨g, hg, k, hk, rfl⟩
    · rw [one_mul]
      exact hb
  inv_mem' := by
    intro a ha
    rcases ha with ⟨g, hg, k, hk, rfl⟩ | rfl
    · refine Or.inl ⟨g, hg, k⁻¹, inv_mem hk, ?_⟩
      group
    · rw [inv_one]
      exact Or.inr rfl

theorem mem_apexRot {G : Type u} [Group G] {X : Type v} [MulAction G X]
    {K : Subgroup G} {c₀ : X}
    {hnorm : ∀ s : G, s • c₀ = c₀ → ∀ k ∈ K, s * k * s⁻¹ ∈ K} {x : X} {h : G} :
    h ∈ apexRot K c₀ hnorm x ↔
      (∃ g : G, g • c₀ = x ∧ ∃ k ∈ K, h = g * k * g⁻¹) ∨ h = 1 := Iff.rfl

/-! ## The three axioms of a rotating family -/

/-- **The orbit of an apex with the conjugates of a fixing subgroup is a
rotating family.**  Invariance of the orbit and equivariance of the assignment
are formal; the fixing axiom is that `K` fixes the apex. -/
theorem isRotatingFamily_apexRot {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (hiso : IsIsometricAction G X)
    (K : Subgroup G) (c₀ : X) (hfix : ∀ k ∈ K, k • c₀ = c₀)
    (hnorm : ∀ s : G, s • c₀ = c₀ → ∀ k ∈ K, s * k * s⁻¹ ∈ K) :
    IsRotatingFamily G X (apexOrbit (G := G) c₀) (apexRot K c₀ hnorm) where
  isometric := hiso
  apex_smul := by
    intro g x hx
    obtain ⟨g₀, rfl⟩ := mem_apexOrbit.mp hx
    exact mem_apexOrbit.mpr ⟨g * g₀, by rw [mul_smul]⟩
  rot_fix := by
    intro c _ h hh
    rcases mem_apexRot.mp hh with ⟨g, hg, k, hk, rfl⟩ | rfl
    · rw [← hg, ← mul_smul, inv_mul_cancel_right, mul_smul, hfix k hk]
    · exact one_smul G c
  rot_equivariant := by
    intro g c _ h
    constructor
    · intro hh
      rcases mem_apexRot.mp hh with ⟨g', hg', k, hk, rfl⟩ | rfl
      · refine mem_apexRot.mpr (Or.inl ⟨g⁻¹ * g', ?_, k, hk, ?_⟩)
        · rw [mul_smul, hg', ← mul_smul, inv_mul_cancel, one_smul]
        · group
      · rw [mul_one, inv_mul_cancel]
        exact mem_apexRot.mpr (Or.inr rfl)
    · intro hh
      rcases mem_apexRot.mp hh with ⟨g', hg', k, hk, hEq⟩ | hEq
      · refine mem_apexRot.mpr (Or.inl ⟨g * g', ?_, k, hk, ?_⟩)
        · rw [mul_smul, hg']
        · have hh : h = g * (g' * k * g'⁻¹) * g⁻¹ := by
            rw [← hEq]
            group
          rw [hh]
          group
      · refine mem_apexRot.mpr (Or.inr ?_)
        have h1 : h = g * (g⁻¹ * h * g) * g⁻¹ := by group
        rw [hEq] at h1
        simpa using h1

/-! ## The two geometric axioms, over the orbit -/

/-- Separation of the orbit, from separation of the translates of the apex. -/
theorem isSeparated_apexOrbit {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {c₀ : X} {ρ : ℝ}
    (hsep : ∀ g g' : G, g • c₀ ≠ g' • c₀ → ρ ≤ dist (g • c₀) (g' • c₀)) :
    IsSeparated (apexOrbit (G := G) c₀) ρ := by
  intro x hx y hy hne
  obtain ⟨g, rfl⟩ := mem_apexOrbit.mp hx
  obtain ⟨g', rfl⟩ := mem_apexOrbit.mp hy
  exact hsep g g' hne

/-- The very rotating axiom, from the same statement for the conjugates of `K`
about the translates of the apex. -/
theorem isVeryRotating_apexRot {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {K : Subgroup G} {c₀ : X} {δ : ℝ}
    {hnorm : ∀ s : G, s • c₀ = c₀ → ∀ k ∈ K, s * k * s⁻¹ ∈ K}
    (hvr : ∀ g k : G, k ∈ K → g * k * g⁻¹ ≠ 1 → ∀ x y : X,
      20 * δ ≤ dist x (g • c₀) → dist x (g • c₀) ≤ 40 * δ →
        20 * δ ≤ dist y (g • c₀) → dist y (g • c₀) ≤ 40 * δ →
          dist ((g * k * g⁻¹) • x) y ≤ 15 * δ →
            ∀ f : ℝ → X, IsGeodesicSegment f 0 (dist x y) → f 0 = x →
              f (dist x y) = y →
                ∃ s ∈ Set.Icc (0 : ℝ) (dist x y), f s = g • c₀) :
    IsVeryRotating G X δ (apexOrbit (G := G) c₀) (apexRot K c₀ hnorm) := by
  intro c _ h hh hne x y h1 h2 h3 h4 h5 f hf hf0 hf1
  rcases mem_apexRot.mp hh with ⟨g, hg, k, hk, rfl⟩ | rfl
  · subst hg
    exact hvr g k hk hne x y h1 h2 h3 h4 h5 f hf hf0 hf1
  · exact absurd rfl hne

/-! ## What the rotations generate -/

/-- **The rotations of the family generate the normal closure of `K`.**  Every
rotation is a conjugate of an element of `K`, and every element of `K` is a
rotation about the apex itself. -/
theorem rotationNormalClosure_apexRot {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {K : Subgroup G} {c₀ : X}
    {hnorm : ∀ s : G, s • c₀ = c₀ → ∀ k ∈ K, s * k * s⁻¹ ∈ K} :
    rotationNormalClosure (apexOrbit (G := G) c₀) (apexRot K c₀ hnorm)
      = Subgroup.normalClosure (K : Set G) := by
  haveI hnrm : (rotationNormalClosure (apexOrbit (G := G) c₀)
      (apexRot K c₀ hnorm)).Normal := by
    show (Subgroup.normalClosure
      {g : G | ∃ c ∈ apexOrbit (G := G) c₀, g ∈ apexRot K c₀ hnorm c}).Normal
    infer_instance
  refine le_antisymm ?_ ?_
  · show Subgroup.normalClosure
      {g : G | ∃ c ∈ apexOrbit (G := G) c₀, g ∈ apexRot K c₀ hnorm c}
      ≤ Subgroup.normalClosure (K : Set G)
    refine Subgroup.normalClosure_le_normal ?_
    rintro h ⟨c, _, hh⟩
    rcases mem_apexRot.mp hh with ⟨g, _, k, hk, rfl⟩ | rfl
    · have hn : (Subgroup.normalClosure (K : Set G)).Normal := inferInstance
      exact SetLike.mem_coe.mpr
        (hn.conj_mem k
          (Subgroup.subset_normalClosure (SetLike.mem_coe.mpr hk)) g)
    · exact SetLike.mem_coe.mpr (Subgroup.one_mem _)
  · refine Subgroup.normalClosure_le_normal ?_
    intro k hk
    refine SetLike.mem_coe.mpr
      (mem_rotationNormalClosure (self_mem_apexOrbit (G := G) c₀) ?_)
    exact mem_apexRot.mpr (Or.inl ⟨1, one_smul G c₀, k, hk, by group⟩)

/-- **The normal closure of a cyclic subgroup is the normal closure of its
generator.**  So a family whose rotations are the conjugates of `⟨w⟩` kills
exactly `w`. -/
theorem normalClosure_zpowers {G : Type u} [Group G] (w : G) :
    Subgroup.normalClosure ((Subgroup.zpowers w : Subgroup G) : Set G)
      = Subgroup.normalClosure ({w} : Set G) := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hw : w ∈ Subgroup.normalClosure ({w} : Set G) :=
      Subgroup.subset_normalClosure rfl
    exact SetLike.mem_coe.mpr (Subgroup.zpow_mem _ hw n)
  · refine Subgroup.normalClosure_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact SetLike.mem_coe.mpr (Subgroup.mem_zpowers w)

/-! ## The cone-off, as the data that is left -/

/-- **The cone-off of `Γ(G, A ⊔ H)` along the conjugates of the axis of the
relator**, as the data the rotating family of Hull's Theorem 5.1 is built from.

Almost everything here is geometry.  The equivariance of the rotation assignment
and the identification of what the rotations generate are *not* fields: they are
`isRotatingFamily_apexRot` and `rotationNormalClosure_apexRot`.

`L` is the displacement below which the quotient has to be faithful, and
`lt_injRadius` is where it is used: the injectivity radius exceeds it.  Both it
and `sep_ge` are arranged the same way, by taking the relator deep enough --
`IsSeparated` is a lower bound and may be shrunk at will.

Two fields are **not** geometry, and both are Hull's §5 rather than DGO's
Theorem 5.3, having been moved out of `HullSC.RotatingQuotient` after being read
against the source: `kernel_moves_base`, the injectivity radius, and
`finiteOrder_lift`, the finite-order lifting clause that issue #50 refuted in
the position it used to occupy.  `HullSCFilling.RotatingData` carries both, and
`toRotatingData` passes them through. -/
structure ConeOffData {G : Type u} [Group G] (A : Alphabet G) (K : Subgroup G)
    (L : ℝ) where
  /-- The cone-off. -/
  Space : Type u
  /-- Its metric. -/
  [metric : PseudoMetricSpace Space]
  /-- The action of `G` on it. -/
  [action : MulAction G Space]
  /-- The action is by isometries. -/
  isometric : IsIsometricAction G Space
  /-- The basepoint, the image of the identity vertex of `Γ(G,A)`. -/
  base : Space
  /-- Every letter of `A` moves the basepoint by at most one. -/
  letter_dist : ∀ a ∈ A.carrier, dist base (a • base) ≤ 1
  /-- The distinguished apex: the cone point over the axis of the relator. -/
  apex : Space
  /-- The rotation subgroup fixes it. -/
  fix : ∀ k ∈ K, k • apex = apex
  /-- It is normal in the stabiliser of the apex.  Over a torsion-free ambient
  group the stabiliser is the cyclic elementary closure of the relator, so this
  is automatic there. -/
  normal_in_stab : ∀ s : G, s • apex = apex → ∀ k ∈ K, s * k * s⁻¹ ∈ K
  /-- The hyperbolicity constant. -/
  delta : ℝ
  /-- It is positive. -/
  delta_pos : 0 < delta
  /-- The cone-off is hyperbolic. -/
  hyperbolic : IsHyperbolicSpace delta Space
  /-- **The cone-off is geodesic.**  DGO work in geodesic spaces throughout, and
  the repaired `HullSC.DGOQuotientStatementGeodesic` asks for it: without one the
  very rotating condition constrains an annulus that can be empty. -/
  isGeodesic : IsGeodesicSpace Space
  /-- The separation of the apices. -/
  sep : ℝ
  /-- Dahmani-Guirardel-Osin's Theorem 5.3 asks for separation above `200 δ`. -/
  sep_ge : 200 * delta ≤ sep
  /-- Distinct apices are `sep` apart. -/
  separated : ∀ g g' : G, g • apex ≠ g' • apex → sep ≤ dist (g • apex) (g' • apex)
  /-- The injectivity radius. -/
  injRadius : ℝ
  /-- It exceeds the prescribed displacement. -/
  lt_injRadius : L < injRadius
  /-- **The injectivity radius, and it is Hull's §5 rather than DGO's.**  Every
  nontrivial element of the normal closure of `K` moves the basepoint by at
  least the injectivity radius.

  Not derivable from the geometry above: DGO's Theorem 5.3 concludes the free
  splitting and the dichotomy, and this follows from neither -- loxodromy is
  asymptotic and gives no bound at the first power, and the splitting is not
  metric.  So it is asked of the cone-off, which is where Hull proves it, and
  `toRotatingData` passes it through.  Quantified over the kernel and stated at
  the basepoint, which is what keeps `HullSC.eq_one_of_dist_lt_everywhere` from
  refuting it: a rotation fixes its apex and lies in the kernel. -/
  kernel_moves_base : ∀ g ∈ Subgroup.normalClosure (K : Set G), g ≠ 1 →
    injRadius ≤ dist base (g • base)
  /-- **Finite order lifts, with the order preserved** -- Hull's §5 as well, and
  for a sharper reason than the last field (issue #50).

  This was a field of `HullSC.RotatingQuotient`, recorded as a conclusion of
  DGO's Theorem 5.3.  `GGT/DGORotatingQuotientRefutation.lean` refutes the
  statement that carried it, and `GGT/DGOFreeSplittingOnePoint.lean` shows the
  refuting model satisfies both of Theorem 5.3's own conclusions, so no route
  from that theorem reaches this clause.  What it needs is control of the
  stabilisers of the action, which the cone-off has and an abstract rotating
  family does not: a vertex of `Γ(G,A)` has trivial stabiliser, and an apex has
  the elementary closure of the relator. -/
  finiteOrder_lift : ∀ {Q : Type u} [Group Q] (q : G →* Q),
    Function.Surjective q → q.ker = Subgroup.normalClosure (K : Set G) →
      ∀ y : Q, IsOfFinOrder y → ∃ g : G, q g = y ∧ orderOf g = orderOf y
  /-- The conjugates of `K` rotate very much about the corresponding apices,
  in the sense of DGO Definition 2.12(c): coupled annulus points are separated
  by the apex on every geodesic between them. -/
  veryRotating : ∀ g k : G, k ∈ K → g * k * g⁻¹ ≠ 1 → ∀ x y : Space,
    20 * delta ≤ dist x (g • apex) → dist x (g • apex) ≤ 40 * delta →
      20 * delta ≤ dist y (g • apex) → dist y (g • apex) ≤ 40 * delta →
        dist ((g * k * g⁻¹) • x) y ≤ 15 * delta →
          ∀ f : ℝ → Space, IsGeodesicSegment f 0 (dist x y) → f 0 = x →
            f (dist x y) = y →
              ∃ s ∈ Set.Icc (0 : ℝ) (dist x y), f s = g • apex

namespace ConeOffData

instance instMetric {G : Type u} [Group G] {A : Alphabet G} {K : Subgroup G}
    {L : ℝ} (P : ConeOffData A K L) : PseudoMetricSpace P.Space := P.metric

instance instAction {G : Type u} [Group G] {A : Alphabet G} {K : Subgroup G}
    {L : ℝ} (P : ConeOffData A K L) : MulAction G P.Space := P.action

/-- **The rotating family of Hull's Theorem 5.1, from the cone-off.**  The
apices are the orbit of the cone point, the rotations are the conjugates of `K`,
and the clauses that are not geometry are passed through along the
identification `hK` of what the rotations generate with `⟨⟨w⟩⟩`. -/
def toRotatingData {G : Type u} [Group G] {A : Alphabet G} {K : Subgroup G}
    {L : ℝ} {w : G} (P : ConeOffData A K L)
    (hK : Subgroup.normalClosure (K : Set G)
      = Subgroup.normalClosure ({w} : Set G)) :
    RotatingData A w L where
  Space := P.Space
  metric := P.metric
  action := P.action
  base := P.base
  letter_dist := P.letter_dist
  delta := P.delta
  delta_pos := P.delta_pos
  hyperbolic := P.hyperbolic
  isGeodesic := P.isGeodesic
  sep := P.sep
  sep_ge := P.sep_ge
  apices := apexOrbit (G := G) P.apex
  rot := apexRot K P.apex P.normal_in_stab
  isRotatingFamily :=
    isRotatingFamily_apexRot P.isometric K P.apex P.fix P.normal_in_stab
  isSeparated := isSeparated_apexOrbit P.separated
  isVeryRotating := isVeryRotating_apexRot P.veryRotating
  rotationNormalClosure_eq := by
    rw [rotationNormalClosure_apexRot, hK]
  injRadius := P.injRadius
  lt_injRadius := P.lt_injRadius
  kernel_moves_base := by
    intro g hg hg1
    refine P.kernel_moves_base g ?_ hg1
    rwa [rotationNormalClosure_apexRot] at hg
  finiteOrder_lift := by
    intro Q _ q hsurj hker
    exact P.finiteOrder_lift q hsurj (hker.trans hK.symm)

end ConeOffData

/-! ## Hull's §5, with the rotating family reduced to the cone-off -/

/-- **Hull's §5, over the cone-off.**  The same statement as
`HullFillingDataStatement`, with the rotating family replaced by the geometry
it is built from: a hyperbolic geodesic `G`-space with an apex whose orbit is
separated, on which the conjugates of `⟨w⟩` are very rotating, and which carries
Hull's own two clauses -- the injectivity radius at the basepoint and the
lifting of finite order.

`K` is `⟨w⟩` rather than an arbitrary subgroup because that is what makes the
kernel come out as `⟨⟨w⟩⟩`: `normalClosure_zpowers`. -/
def HullConeOffStatement : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore A N), Suitable A.alphabet N →
      ∀ {k : ℕ} (S : Fin k → Subgroup G),
        (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ R : ℕ,
          ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
            ∀ (W : Set (List (GGT.RelLetter G Unit)))
              (v : List (GGT.RelLetter G Unit)), v ∈ W →
              RelWord.IsSmallCancellation E.rel W eps mu rho →
                Nonempty (ConeOffData A.alphabet
                    (Subgroup.zpowers (GGT.RelLetter.listVal v))
                    (2 * (R : ℝ))) ∧
                  ∀ {Q : Type u} [Group Q] (q : G →* Q), Function.Surjective q →
                    q.ker = Subgroup.normalClosure
                        ({GGT.RelLetter.listVal v} : Set G) →
                      Nonempty (FillingAlphabetData A N S q)

/-- **Hull's §5 from the cone-off.**  `ConeOffData.toRotatingData` supplies the
rotating family, and `normalClosure_zpowers` identifies what its rotations
generate with the normal closure of the relator. -/
theorem hullFillingDataStatement_of_coneOff (h : HullConeOffStatement.{u}) :
    HullFillingDataStatement.{u} := by
  intro G _ A N E hN k S hS R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := h A N E hN S hS R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hsc
  obtain ⟨⟨P⟩, halph⟩ := hgood W v hv hsc
  exact ⟨⟨P.toRotatingData (normalClosure_zpowers _)⟩, halph⟩

/-- **Hull's Theorem 5.1 from the cone-off and DGO's Theorem 5.3**, the latter
in its repaired form: the cone-off is geodesic, which is what
`DGOQuotientStatementGeodesic` asks for and what the vertex model of `Γ(G,A)`
cannot supply. -/
theorem hullQuotient_of_coneOff (hDGO : DGOQuotientStatementGeodesic.{u, u})
    (h : HullConeOffStatement.{u}) : HullQuotientStatement.{u} :=
  hullQuotient_of_fillingData hDGO (hullFillingDataStatement_of_coneOff h)

end HullSC
end GroupApproximation
