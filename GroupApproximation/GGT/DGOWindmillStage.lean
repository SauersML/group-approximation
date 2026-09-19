import GroupApproximation.GGT.DGOWindmillSpokes
import GroupApproximation.GGT.DGOWindmillFree

/-!
# One stage of the growth: the new apices and their reference sets

Tenth module of the campaign aimed at
`Manuscript.NonMF.TheoremCAssembly.dgoTheorem53` (DGO's Theorem 5.3(b)).

`GGT/DGOWindmillPath.lean` proves the broken path of a reduced word is geodesic,
but it takes the reference sets `S d` of the corner lemma as *given*, with three
properties: each is `12δ`-quasiconvex, each sits `55δ` from its own apex, and
each contains every other new apex.  This module makes the concrete choice and
discharges all three.

## The choice, and the arithmetic that forces it

    C₁ = { c ∈ C | c ∉ W  and  d(c, W) ≤ 76δ }        the new apices
    W₁ = spokeSet W C₁ 76δ                             DGO's `W ∪ ⋃ [c, c̄]`
    S d = spokeSet W (C₁ \ {d}) 76δ                    the reference set at `d`

Every constant here is pinned by an inequality, and the campaign has no freedom
in any of them:

* `S d` is `12δ`-quasiconvex because `W` is `6δ`-quasiconvex --- that is the
  spoke estimate, and its independence from the reach `76δ` is what keeps the
  induction from diverging.
* `55δ ≤ d(d, S d)` needs two bounds.  On the `W` part it is exactly the
  windmill's `far` clause.  On the spokes it needs `55δ + 76δ ≤ ρ`, i.e.
  `131δ ≤ 200δ`, because a point of a spoke is within its reach of a tip and
  distinct apices are `ρ` apart.  This is the inequality that caps the reach:
  a reach above `145δ` would break it.
* An apex outside `W₁` is `75δ` from it --- `75δ` on the `W` part because such an
  apex is more than `76δ` from `W` by the definition of `C₁`, and
  `75δ + 76δ ≤ 200δ` on the spokes.  This is the inequality that floors the
  reach, and `75δ` is the budget the next stage's `far` clause spends: it has to
  survive the `18δ` thickening that produces `W'` and still clear `55δ`.

So the reach is squeezed between roughly `73δ` and `145δ`, and `76δ` sits inside
with room on both sides.  DGO's `60δ` does not: with the `55δ` this repository's
`far` clause carries, a reach of `60δ` leaves only `59δ` for the next stage,
which the thickening eats.

## What is *not* here

The quasiconvexity of the unfolded windmill `W₂ = G₂ · W₁`, and hence axiom 1
for `W'`, is not proved here, because it is a consequence of the broken path
being geodesic and therefore depends on `GGT/DGOWindmillPath.lean` and through it
on the word algebra.  Everything in this module is independent of both.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-! ## The new apices of a stage -/

/-- **The apices the stage attaches**: those outside the windmill but within
reach `76δ` of it.  The reach is measured by a witness in `W` rather than by an
infimum, so that no `Metric.infDist` has to be unfolded and so that invariance
under the windmill group is the isometry applied to the witness. -/
def newApices (δ : ℝ) (C W : Set X) : Set X :=
  {c : X | c ∈ C ∧ c ∉ W ∧ ∃ w ∈ W, dist c w ≤ 76 * δ}

theorem mem_newApices_iff {δ : ℝ} {C W : Set X} {c : X} :
    c ∈ newApices δ C W ↔ c ∈ C ∧ c ∉ W ∧ ∃ w ∈ W, dist c w ≤ 76 * δ := Iff.rfl

theorem newApices_subset {δ : ℝ} {C W : Set X} : newApices δ C W ⊆ C :=
  fun _ hc => (mem_newApices_iff.mp hc).1

theorem not_mem_of_mem_newApices {δ : ℝ} {C W : Set X} {c : X}
    (hc : c ∈ newApices δ C W) : c ∉ W := (mem_newApices_iff.mp hc).2.1

/-- **An apex neither in the windmill nor attached is more than `76δ` from every
point of the windmill.**  The contrapositive of the reach condition. -/
theorem lt_dist_of_not_mem_newApices {δ : ℝ} {C W : Set X} {c : X} (hc : c ∈ C)
    (hcW : c ∉ W) (hnew : c ∉ newApices δ C W) : ∀ w ∈ W, 76 * δ < dist c w := by
  intro w hw
  by_contra hle
  exact hnew ⟨hc, hcW, w, hw, not_lt.mp hle⟩

/-- The windmill group carries new apices to new apices: it preserves the apex
set, preserves the windmill, and moves a reach witness to a reach witness. -/
theorem smul_mem_newApices {δ : ℝ} {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot) {W : Set X}
    (hW : IsWindmill G X δ C Rot W) {a : G} (ha : a ∈ windmillGroup C Rot W)
    {d : X} (hd : d ∈ newApices δ C W) : a • d ∈ newApices δ C W := by
  obtain ⟨hdC, hdW, hreach⟩ := mem_newApices_iff.mp hd
  obtain ⟨hC, hW'⟩ := smul_mem_diff_of_isWindmill hfam hW ha hdC hdW
  exact ⟨hC, hW', exists_mem_dist_le_smul_of_isWindmill hfam hW ha hreach⟩

/-! ## The reference set of a new apex -/

/-- **The reference set at a new apex `d`**: the windmill together with the
spokes at every *other* new apex.  DGO's `W ∪ ⋃_{c ∈ C₁ \ {d}} [c, c̄]`, which
their Lemma 5.15 calls `W'₁`.

The spokes at `d` itself have to be omitted, and that is the whole reason the
reference set is not simply `W₁`: a spoke at `d` reaches `d`, so `W₁` is not far
from `d` and the corner lemma's second hypothesis would fail. -/
def stageRef (δ : ℝ) (C W : Set X) (d : X) : Set X :=
  spokeSet W {e : X | e ∈ newApices δ C W ∧ e ≠ d} (76 * δ)

/-- Every other new apex lies in the reference set: it is a tip of one of the
spokes that were kept. -/
theorem mem_stageRef_of_mem_newApices {δ : ℝ} {C W : Set X} {d e : X}
    (he : e ∈ newApices δ C W) (hne : e ≠ d) : e ∈ stageRef δ C W d := by
  obtain ⟨-, -, w, hw, hew⟩ := mem_newApices_iff.mp he
  exact mem_spokeSet_of_mem_tips ⟨he, hne⟩ hw hew

/-- **The reference set is `12δ`-quasiconvex**, from the windmill's own `6δ` and
the spoke estimate, with a constant independent of the reach. -/
theorem isQuasiconvexSet_stageRef {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X) {C : Set X}
    {Rot : X → Subgroup G} {W : Set X} (hW : IsWindmill G X δ C Rot W) (d : X) :
    IsQuasiconvexSet (stageRef δ C W d) (12 * δ) :=
  isQuasiconvexSet_spokeSet hδ0 hhyp hgeo hW.quasiconvex

/-- **The reference set stays `55δ` from its own apex.**

On the windmill this is the `far` clause verbatim.  On a spoke it is the
separation of the family: a point of a spoke is within the reach `76δ` of its
tip, the tip is another apex, and distinct apices are `ρ ≥ 200δ` apart, so
`55δ + 76δ = 131δ ≤ 200δ` closes it.

This is the corner lemma's second hypothesis, and it is the inequality that caps
how far a stage may reach. -/
theorem le_dist_of_mem_stageRef {δ ρ : ℝ} (hδ0 : 0 ≤ δ) (hρ : 200 * δ ≤ ρ)
    {C : Set X} {Rot : X → Subgroup G} {W : Set X}
    (hW : IsWindmill G X δ C Rot W) (hsep : IsSeparated C ρ) {d : X}
    (hd : d ∈ newApices δ C W) : ∀ z ∈ stageRef δ C W d, 55 * δ ≤ dist d z := by
  obtain ⟨hdC, hdW, -⟩ := mem_newApices_iff.mp hd
  have hAfar : ∀ e ∈ {e : X | e ∈ newApices δ C W ∧ e ≠ d},
      55 * δ + 76 * δ ≤ dist d e := by
    intro e he
    obtain ⟨heNew, hne⟩ := he
    have hsepde : ρ ≤ dist d e :=
      hsep d hdC e (newApices_subset heNew) (Ne.symm hne)
    linarith
  intro z hz
  exact le_dist_of_mem_spokeSet (fun w hw => hW.far d hdC hdW w hw) hAfar hz

/-! ## The stage's own spoke set -/

/-- `W₁`, the windmill with a spoke at every new apex.  DGO's `W₁`. -/
def stageOne (δ : ℝ) (C W : Set X) : Set X :=
  spokeSet W (newApices δ C W) (76 * δ)

theorem subset_stageOne {δ : ℝ} {C W : Set X} : W ⊆ stageOne δ C W :=
  subset_spokeSet

theorem newApices_subset_stageOne {δ : ℝ} {C W : Set X} :
    newApices δ C W ⊆ stageOne δ C W := by
  intro e he
  obtain ⟨-, -, w, hw, hew⟩ := mem_newApices_iff.mp he
  exact mem_spokeSet_of_mem_tips he hw hew

theorem stageRef_subset_stageOne {δ : ℝ} {C W : Set X} {d : X} :
    stageRef δ C W d ⊆ stageOne δ C W :=
  spokeSet_mono_tips fun _ he => he.1

theorem isQuasiconvexSet_stageOne {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X) {C : Set X}
    {Rot : X → Subgroup G} {W : Set X} (hW : IsWindmill G X δ C Rot W) :
    IsQuasiconvexSet (stageOne δ C W) (12 * δ) :=
  isQuasiconvexSet_spokeSet hδ0 hhyp hgeo hW.quasiconvex

/-- **An apex the stage does not attach stays `75δ` from everything the stage
builds.**

On the windmill it is more than `76δ` away by the definition of `newApices`; on a
spoke, `75δ + 76δ = 151δ ≤ 200δ ≤ ρ`.

`75δ` is the budget the next stage's `far` clause spends.  It has to survive the
thickening that turns the unfolded windmill into `W'` and still clear the `55δ`
that `far` demands, which is what fixes the thickening at `18δ`: `75 - 18 = 57`,
and `57 ≥ 55`. -/
theorem le_dist_of_mem_stageOne {δ ρ : ℝ} (hδ0 : 0 ≤ δ) (hρ : 200 * δ ≤ ρ)
    {C : Set X} {W : Set X} (hsep : IsSeparated C ρ) {c : X} (hc : c ∈ C)
    (hcW : c ∉ W) (hnew : c ∉ newApices δ C W) :
    ∀ p ∈ stageOne δ C W, 75 * δ ≤ dist c p := by
  have hWfar : ∀ w ∈ W, 75 * δ ≤ dist c w := by
    intro w hw
    have h := lt_dist_of_not_mem_newApices hc hcW hnew w hw
    linarith
  have hAfar : ∀ e ∈ newApices δ C W, 75 * δ + 76 * δ ≤ dist c e := by
    intro e heNew
    have hneq : c ≠ e := by
      intro h
      apply hnew
      rw [h]
      exact heNew
    have hsepce : ρ ≤ dist c e := hsep c hc e (newApices_subset heNew) hneq
    linarith
  intro p hp
  exact le_dist_of_mem_spokeSet hWfar hAfar hp

end DGOWindmill
end GroupApproximation
