import GroupApproximation.Leavitt.MatrixSelfSimilarity
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone: elementary units over an arbitrary ring

Khanh (arXiv:2609.08428), proof of Prop. `prop:frame-cone`, eq. `cone-coordinate-inverses`:

> `(w,t,z) ↦ w + vt + σ_i z` and `u ↦ ((I-σ_iρ_i)u - w_i b_iρ_i u, b_iρ_i u, ρ_i u - y_i b_iρ_i u)`

After scalarizing `A^4 ≅ A`, the coordinate change is a product of three units, built here
over an arbitrary ring:

* `cornerUnit`: for `ρσ = 1` and a unit `u`, `1 - σρ + σuρ` acts by `u` on `σA` and fixes
  `ker ρ`;
* `shearUnit`: for `c w = 0`, `1 + w c` is a unit (used with `w = (1-σρ)p`, `c = bρ`, which
  sends `σρp` to `p` when `bρp = 1` and fixes `ker ρ`);
* `permUnit`: for a complete matrix family and a permutation `π`, `Σ_i left (π i) right i`
  is a unit sending `left j` to `left (π j)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone

open GroupApproximation

variable {A : Type*} [Ring A]

/-- The corner element `1 - σρ + σuρ`. -/
def cornerElt (σ ρ u : A) : A := 1 - σ * ρ + σ * u * ρ

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.cornerElt

theorem cornerElt_mul {σ ρ : A} (hρσ : ρ * σ = 1) (u v : A) :
    cornerElt σ ρ u * cornerElt σ ρ v = cornerElt σ ρ (u * v) := by
  calc
    cornerElt σ ρ u * cornerElt σ ρ v =
        1 - σ * ρ + σ * v * ρ - σ * ρ + σ * (ρ * σ) * ρ - σ * (ρ * σ) * v * ρ + σ * u * ρ
          - σ * u * (ρ * σ) * ρ + σ * u * (ρ * σ) * v * ρ := by
      unfold cornerElt
      noncomm_ring
    _ = cornerElt σ ρ (u * v) := by
      rw [hρσ]
      unfold cornerElt
      noncomm_ring

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.cornerElt_mul

theorem cornerElt_one (σ ρ : A) : cornerElt σ ρ 1 = 1 := by
  unfold cornerElt
  noncomm_ring

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.cornerElt_one

/-- The corner unit `1 - σρ + σuρ` of a unit `u`, when `ρσ = 1`. -/
def cornerUnit {σ ρ : A} (hρσ : ρ * σ = 1) (u : Aˣ) : Aˣ :=
  ⟨cornerElt σ ρ u, cornerElt σ ρ ↑u⁻¹,
    by rw [cornerElt_mul hρσ, Units.mul_inv, cornerElt_one],
    by rw [cornerElt_mul hρσ, Units.inv_mul, cornerElt_one]⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.cornerUnit

theorem cornerUnit_mul_of_rho {σ ρ : A} (hρσ : ρ * σ = 1) (u : Aˣ) {x : A}
    (hx : ρ * x = 0) : (cornerUnit hρσ u : A) * x = x := by
  change cornerElt σ ρ u * x = x
  calc
    cornerElt σ ρ u * x = x - σ * (ρ * x) + σ * u * (ρ * x) := by
      unfold cornerElt
      noncomm_ring
    _ = x := by
      rw [hx]
      noncomm_ring

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.cornerUnit_mul_of_rho

theorem cornerUnit_mul_sigma {σ ρ : A} (hρσ : ρ * σ = 1) (u : Aˣ) (c : A) :
    (cornerUnit hρσ u : A) * (σ * c) = σ * ((u : A) * c) := by
  change cornerElt σ ρ u * (σ * c) = σ * ((u : A) * c)
  calc
    cornerElt σ ρ u * (σ * c) = σ * c - σ * (ρ * σ) * c + σ * u * (ρ * σ) * c := by
      unfold cornerElt
      noncomm_ring
    _ = σ * ((u : A) * c) := by
      rw [hρσ]
      noncomm_ring

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.cornerUnit_mul_sigma

/-- The shear `1 + w c`, a unit when `c w = 0`. -/
def shearUnit {w c : A} (hcw : c * w = 0) : Aˣ :=
  ⟨1 + w * c, 1 - w * c,
    by
      calc
        (1 + w * c) * (1 - w * c) = 1 - w * (c * w) * c := by noncomm_ring
        _ = 1 := by
          rw [hcw]
          noncomm_ring,
    by
      calc
        (1 - w * c) * (1 + w * c) = 1 - w * (c * w) * c := by noncomm_ring
        _ = 1 := by
          rw [hcw]
          noncomm_ring⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.shearUnit

theorem shearUnit_val {w c : A} (hcw : c * w = 0) : (shearUnit hcw : A) = 1 + w * c := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.shearUnit_val

/-- The shear used by the frame cone kills `bρ(1-σρ)p` because `ρσ = 1`. -/
theorem cone_shear_orth {σ ρ : A} (hρσ : ρ * σ = 1) (b p : A) :
    b * ρ * ((1 - σ * ρ) * p) = 0 := by
  calc
    b * ρ * ((1 - σ * ρ) * p) = b * ρ * p - b * (ρ * σ) * ρ * p := by noncomm_ring
    _ = 0 := by
      rw [hρσ]
      noncomm_ring

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.cone_shear_orth

theorem cone_shear_of_rho {σ ρ : A} (hρσ : ρ * σ = 1) (b p : A) {x : A} (hx : ρ * x = 0) :
    (shearUnit (cone_shear_orth hρσ b p) : A) * x = x := by
  rw [shearUnit_val]
  calc
    (1 + (1 - σ * ρ) * p * (b * ρ)) * x = x + (1 - σ * ρ) * p * b * (ρ * x) := by noncomm_ring
    _ = x := by
      rw [hx]
      noncomm_ring

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.cone_shear_of_rho

theorem cone_shear_sigma {σ ρ : A} (hρσ : ρ * σ = 1) (b p : A) (hb : b * (ρ * p) = 1) :
    (shearUnit (cone_shear_orth hρσ b p) : A) * (σ * (ρ * p)) = p := by
  rw [shearUnit_val]
  calc
    (1 + (1 - σ * ρ) * p * (b * ρ)) * (σ * (ρ * p)) =
        σ * (ρ * p) + (1 - σ * ρ) * p * b * ((ρ * σ) * (ρ * p)) := by noncomm_ring
    _ = σ * (ρ * p) + (1 - σ * ρ) * p * (b * (ρ * p)) := by
      rw [hρσ]
      noncomm_ring
    _ = p := by
      rw [hb]
      noncomm_ring

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone.cone_shear_sigma

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameCone
