import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanSentenceAudit

/-!
# Restricting corrected-corner data to a Kazhdan subgroup

The ambient group in the normal-Kazhdan theorem need not have property (T).
The printed corner data therefore has to be pulled back along the inclusion of
the normal Kazhdan subgroup before applying the corrected-corner Kazhdan
bridge.  This file records that restriction and its exact compatibility with
the corner models, compressions, and polar-corrected maps.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix PrintedCornerCompression
open MaximalCStarKazhdanProjection
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

variable {G : Type u} [Group G] {K : Type v} [Group K]
variable {model : ℕ → FiniteModel}

/-- Pull an ambient corrected-corner construction back along a group
homomorphism.  The projections and hence the corner coordinates are unchanged;
only the unitary family is precomposed. -/
def printedCornerDataPullback (D : PrintedCornerData G model) (iota : K →* G) :
    PrintedCornerData K model where
  V n k := D.V n (iota k)
  q := D.q
  q_projection := D.q_projection
  q_ne_zero := D.q_ne_zero
  mul_vanishing k l := by
    simpa only [map_mul] using D.mul_vanishing (iota k) (iota l)
  commutator_vanishing k := D.commutator_vanishing (iota k)

@[simp]
theorem printedCornerDataPullback_V
    (D : PrintedCornerData G model) (iota : K →* G)
    (n : ℕ) (k : K) :
    (printedCornerDataPullback D iota).V n k = D.V n (iota k) := rfl

@[simp]
theorem printedCornerDataPullback_q
    (D : PrintedCornerData G model) (iota : K →* G)
    (n : ℕ) :
    (printedCornerDataPullback D iota).q n = D.q n := rfl

/-- Restriction does not change the finite corner model. -/
@[simp]
theorem printedCornerDataPullback_cornerModel
    (D : PrintedCornerData G model)
    (iota : K →* G) (n : ℕ) :
    (printedCornerDataPullback D iota).cornerModel n = D.cornerModel n := rfl

/-- The restricted compression is literally the ambient compression evaluated
on the image of the subgroup element. -/
@[simp]
theorem printedCornerDataPullback_compress
    (D : PrintedCornerData G model)
    (iota : K →* G) (n : ℕ) (k : K) :
    (printedCornerDataPullback D iota).compress n k =
      D.compress n (iota k) := rfl

/-- Polar correction commutes definitionally with restriction to the subgroup. -/
@[simp]
theorem printedCornerDataPullback_cornerMap
    (D : PrintedCornerData G model)
    (iota : K →* G) (n : ℕ) (k : K) :
    ((printedCornerDataPullback D iota).cornerMap n k :
      Matrix ((printedCornerDataPullback D iota).cornerModel n)
        ((printedCornerDataPullback D iota).cornerModel n) ℂ) =
      (D.cornerMap n (iota k) :
        Matrix (D.cornerModel n) (D.cornerModel n) ℂ) := rfl

/-- The fixed-element conclusion for a normal Kazhdan subgroup, without
strengthening the ambient group to property (T).  The analytic bridge is
applied to the pullback of the ambient corner data along `iota`. -/
theorem manuscriptNormalKazhdanSubgroup_correctedCornerDetection
    {G K : Type} [Group G] [Group K] {model : ℕ → FiniteModel}
    (D : PrintedCornerData G model) (iota : K →* G)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (KD : KazhdanData K)
    (hzero : CorrectedCornerKazhdanProjectionZero
      (printedCornerDataPullback D iota) ω hω KD) :
    ∃ k0 ∈ KD.S, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ n,
        0 < KD.kappa ^ 2 / (2 * KD.S.card) ∧
          KD.kappa ^ 2 / (2 * KD.S.card) ≤
            hsNormSq (D.cornerModel (phi n))
              ((D.cornerMap (phi n) (iota k0) :
                Matrix (D.cornerModel (phi n))
                  (D.cornerModel (phi n)) ℂ) - 1) := by
  obtain ⟨k0, hk0, phi, hphi, hbound⟩ :=
    manuscriptSentence156_correctedCornerKazhdanDetection
      (printedCornerDataPullback D iota) ω hω KD hzero
  refine ⟨k0, hk0, phi, hphi, fun n ↦ ?_⟩
  change 0 < KD.kappa ^ 2 / (2 * KD.S.card) ∧
    KD.kappa ^ 2 / (2 * KD.S.card) ≤
      hsNormSq ((printedCornerDataPullback D iota).cornerModel (phi n))
        (((printedCornerDataPullback D iota).cornerMap (phi n) k0 :
          Matrix ((printedCornerDataPullback D iota).cornerModel (phi n))
            ((printedCornerDataPullback D iota).cornerModel (phi n)) ℂ) - 1)
  exact hbound n

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
