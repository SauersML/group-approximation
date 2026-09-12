import GroupApproximation.CharClass.LerayHirschChartClassIso
import GroupApproximation.CharClass.LerayHirschChartClassGenK
import GroupApproximation.CharClass.ChernEulerIsoOf

/-!
# The class identification over a coefficient field

The coefficient-generic form of `LerayHirschChartClassIso.pull_prodIso_cpGen`.

Over `F₂` the fibre class is `cpGen r hr`, and the index change from `ℂP^r` to the large projective
space the tautological class is computed in is absorbed by the fact that the stable inclusion
carries `cpGen` to `cpGen`.  Over `K` there is no canonical generator, so the fibre class is
*defined* to be what the tautological class restricts to: the Euler class, relative to the chosen
`hgen ∈ H^2(ℂP^N; K)`, of the tautological line of `ℂP^r` pushed into `ℂP^N`.  Pushing along
`Fin.castLE` needs no cast on `N`, and `CPn.eulerOfBundle_pushforward_congrOf` says the choice of
injection is immaterial, so no dependent transport appears in any statement.

The fibre class is nonzero as soon as `hgen` is: pushing along `iterFin` instead, its classifying
map is the iterated hyperplane inclusion, which is bijective on `H^2(-; K)`
(`ProjectiveSpaceStableOf.bijective_pull_cpInclIterOf`).

## Main declarations

* `LH.cpCoordEmbOf`, `LH.fibClassOf` — **the fibre class over `K`**.
* `LH.fibClassOf_eq_pull_cpInclIter`, `LH.fibClassOf_ne_zero`.
* `LH.pull_prodIso_fibClassOf` — **the class identification**, at any isomorphism of situations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn

noncomputable section

/-! ## 1. The fibre class -/

/-- The inclusion of the coordinates of `ℂP^r` into those of `ℂP^N`, for `r ≤ N`. -/
def cpCoordEmbOf (N r : ℕ) (h : r ≤ N) : Fin (r + 1) → Fin (N + 1) :=
  Fin.castLE (by omega)

theorem cpCoordEmbOf_injective (N r : ℕ) (h : r ≤ N) :
    Function.Injective (cpCoordEmbOf N r h) :=
  Fin.castLE_injective _

/-- **The fibre class over `K`**: the Euler class, relative to `hgen ∈ H^2(ℂP^N; K)`, of the
tautological line of `ℂP^r` pushed into `ℂP^N`. -/
def fibClassOf (K : Type) [CommRing K] {N : ℕ} (hgen : Hmod K (CPtop N) 2) (r : ℕ)
    (h : r ≤ N) : Hmod K (CPtop r) 2 :=
  eulerOfBundleOf K hgen
    (pushforward (cpCoordEmbOf N r h) (cpCoordEmbOf_injective N r h) (cpTaut r))
    (trace_pushforward_one (cpCoordEmbOf N r h) (cpCoordEmbOf_injective N r h) (cpTaut r)
      (trace_cpTaut r))

/-- **The fibre class is the pullback of `hgen` along the iterated hyperplane inclusion.** -/
theorem fibClassOf_eq_pull_cpInclIter (K : Type) [Field K] (r k : ℕ) (hr : 1 ≤ r)
    (hgen : Hmod K (CPtop (r + k)) 2) (h : r ≤ r + k) :
    fibClassOf K hgen r h = pull (cpInclIter r k) 2 hgen := by
  have h1 := CPn.eulerOfBundle_pushforward_congrOf K (show 1 ≤ r + k by omega) hgen
    (cpTaut r) (cpTaut r) (cpCoordEmbOf_injective (r + k) r h) (CPn.iterFin_injective r k)
    (trace_pushforward_one _ (cpCoordEmbOf_injective (r + k) r h) (cpTaut r) (trace_cpTaut r))
    (trace_pushforward_one _ (CPn.iterFin_injective r k) (cpTaut r) (trace_cpTaut r))
    (BundleIso.refl (cpTaut r))
  rw [fibClassOf, h1, eulerOfBundleOf, eulerClassOf,
    classifyOne_pushforward (cpTaut r) (trace_cpTaut r) (CPn.iterFin_injective r k),
    cpEmbed_congr _ (iterMat_isometry r k) (iterMat_eq_coordIncl r k).symm,
    classifyOne_cpTaut, cpInclIter_eq_cmap_cpEmbed]
  rfl

/-- **The fibre class is nonzero when `hgen` is**, for `1 ≤ r`. -/
theorem fibClassOf_ne_zero (K : Type) [Field K] {N : ℕ} (hgen : Hmod K (CPtop N) 2)
    (hgen0 : hgen ≠ 0) {r : ℕ} (hr : 1 ≤ r) (h : r ≤ N) : fibClassOf K hgen r h ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [fibClassOf_eq_pull_cpInclIter K r k hr hgen h]
  intro h0
  exact hgen0 ((bijective_pull_cpInclIterOf K r hr k).1 (h0.trans (pull_zero _ 2).symm))

/-! ## 2. The class identification -/

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The class identification over `K`, at any isomorphism of situations.**  Under an
isomorphism of the part over `U` with a product, compatible with the projection to `ℂP^r` and
with the tautological lines, the tautological class relative to `hgen` restricts to the
pulled-back fibre class. -/
theorem pull_prodIso_fibClassOf (K : Type) [Field K] (p : Bundle X ι)
    (U : Opens (TopCat.of X)) (r : ℕ)
    (E : opSpace (opensComap (projMapOf p) U)
      ≅ TopCat.of (↥((U : Opens (TopCat.of X)) : Set X) × CP r))
    (chartCP : C(↥(opSpace (opensComap (projMapOf p) U)), CP r))
    (hchart : cmap chartCP = E.hom ≫ KnCP.cpSnd _ r)
    (chartIncl : C(↥(opSpace (opensComap (projMapOf p) U)), Proj p))
    (hincl : LH.opIncl (opensComap (projMapOf p) U) = cmap chartIncl)
    (hrc : r ≤ 1 + tautCardOf ι)
    (etaut : BundleIso (comap chartIncl (tautLine p)) (comap chartCP (cpTaut r)))
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) :
    pull E.hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (fibClassOf K hgen r hrc))
      = lhClass (projMapOf p) (tautEulerOfK K hgen p) U := by
  have hL : pull E.hom 2
        (pull (KnCP.cpSnd ↥((U : Opens (TopCat.of X)) : Set X) r) 2 (fibClassOf K hgen r hrc))
      = eulerOfBundleOf K hgen
          (pushforward (cpCoordEmbOf _ r hrc) (cpCoordEmbOf_injective _ r hrc)
            (comap chartCP (cpTaut r)))
          (fun w => trace_pushforward_one (cpCoordEmbOf _ r hrc)
            (cpCoordEmbOf_injective _ r hrc) (cpTaut r) (trace_cpTaut r) (chartCP w)) := by
    rw [← pull_comp, ← hchart, fibClassOf, ← eulerOfBundle_comapOf]
    rfl
  have hR : lhClass (projMapOf p) (tautEulerOfK K hgen p) U
      = eulerOfBundleOf K hgen
          (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) (comap chartIncl (tautLine p)))
          (fun w => trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι)
            (tautLine p) (trace_tautLine p) (chartIncl w)) := by
    rw [lhClass, hincl, tautEulerOfK, ← eulerOfBundle_comapOf]
    rfl
  rw [hL, hR]
  exact CPn.eulerOfBundle_pushforward_congrOf K (show 1 ≤ 1 + tautCardOf ι by omega) hgen _ _
    (cpCoordEmbOf_injective _ r hrc) (tautEmbOf_injective ι) _ _ etaut.symm

end

end LH
end CharClass
end GroupApproximation
