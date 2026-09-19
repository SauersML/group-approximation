import GroupApproximation.CharClass.CohomologyKunnethParity
import GroupApproximation.CharClass.ProjectiveSpaceCover

/-!
# The chart cover of a product with a projective space

The projective-factor Künneth runs the same Mayer–Vietoris argument as the sphere
one, over the cover of `U × ℂP^{d+1}` by `U × (affine chart)` and
`U × (ℂP^{d+1} ∖ pt)`.  This file is the chart-cover analogue of
`CohomologyKunnethHemi` and `CohomologyKunnethBand`: the cover, the three pieces
identified through the projection to `U`, and the compatibilities.

The three identifications are `cc-projective`'s, crossed with `U`:

* the chart is contractible, so `U × chart` is `U` **through the projection**;
* the punctured projective space retracts to the hyperplane, so `U × punct` is
  `U × ℂP^d`;
* the intersection is the odd sphere, so it is `U × S^{2d+1}`, where the sphere
  Künneth applies.

## Main declarations

* `KnCP.chartU`, `KnCP.punctU`, `KnCP.cp_sup` — the cover.
* `KnCP.cpPrSub` — the projection of a piece to `U`.
* `KnCP.exists_pull_cpPrSub_chart` — the chart analogue of
  `KnHemi.exists_pull_prSub_hemiU`.
* `KnCP.punctHomotopyEquiv`, `KnCP.interHomotopyEquiv` — the other two pieces.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

instance contractible_chartOpen_coe :
    ContractibleSpace ↥((chartOpen d : Opens (CPtop (d + 1)))
      : Set ↥(CPtop (d + 1))) :=
  contractibleSpace_chartOpen d

/-- `U × ℂP^{d+1}` as an object of `TopCat`. -/
abbrev cpProdTop : TopCat.{0} := TopCat.of (U × CP (d + 1))

/-- The projection to `U`. -/
abbrev cpPrU : cpProdTop U d ⟶ TopCat.of U := cmap ContinuousMap.fst

abbrev chartU : Opens ↥(cpProdTop U d) := prodOpen U (chartOpen d)
abbrev punctU : Opens ↥(cpProdTop U d) := prodOpen U (punctOpen d)
abbrev chartUSet : Set ↥(cpProdTop U d) := (chartU U d : Set ↥(cpProdTop U d))
abbrev punctUSet : Set ↥(cpProdTop U d) := (punctU U d : Set ↥(cpProdTop U d))
abbrev interUSet : Set ↥(cpProdTop U d) := chartUSet U d ∩ punctUSet U d

theorem cp_sup : chartU U d ⊔ punctU U d = ⊤ :=
  prodOpen_sup U (chartOpen_sup_punctOpen d)

/-! ## 1. The projection of a piece to `U` -/

/-- The projection to `U` of a subspace of `U × ℂP^{d+1}`. -/
def cpPrSub (S : Set ↥(cpProdTop U d)) : TopCat.of ↥S ⟶ TopCat.of U :=
  cmap ⟨fun p => (p : U × CP (d + 1)).1,
    continuous_fst.comp continuous_subtype_val⟩

theorem sInclusion_comp_cpPrSub (S : Set ↥(cpProdTop U d)) :
    sInclusion S ≫ cpPrU U d = cpPrSub U d S := rfl

theorem subInclusion_comp_cpPrSub {S T : Set ↥(cpProdTop U d)} (h : S ⊆ T) :
    subInclusion h ≫ cpPrSub U d T = cpPrSub U d S := rfl

/-! ## 2. The chart piece is `U` -/

/-- `U × (affine chart)` is homotopy equivalent to `U`. -/
def chartHomotopyEquiv : ContinuousMap.HomotopyEquiv ↥(chartUSet U d) U :=
  (prodSubtypeHomeo U
      ((chartOpen d : Opens (CPtop (d + 1)))
        : Set ↥(CPtop (d + 1)))).toHomotopyEquiv.trans
    (prodContractibleEquiv U
      ↥((chartOpen d : Opens (CPtop (d + 1))) : Set ↥(CPtop (d + 1))))

theorem chartHomotopyEquiv_toFun :
    (chartHomotopyEquiv U d).toFun = (cpPrSub U d (chartUSet U d)).hom := by
  ext p
  rfl

theorem cpPrSub_chart_eq :
    cpPrSub U d (chartUSet U d) = cmap (chartHomotopyEquiv U d).toFun :=
  (TopCat.Hom.ext (chartHomotopyEquiv_toFun U d)).symm

/-- **The chart analogue of `KnHemi.exists_pull_prSub_hemiU`.**  Every class on the
chart piece is pulled back from `U`. -/
theorem exists_pull_cpPrSub_chart (m : ℕ)
    (a : Hmod2 (TopCat.of ↥(chartUSet U d)) m) :
    ∃ c : Hmod2 (TopCat.of U) m, pull (cpPrSub U d (chartUSet U d)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquiv (chartHomotopyEquiv U d) m).symm a, ?_⟩
  rw [cpPrSub_chart_eq]
  exact (pullEquivOfHomotopyEquiv (chartHomotopyEquiv U d) m).apply_symm_apply a

/-! ## 3. The punctured piece is `U × ℂP^d`, the intersection is `U × S^{2d+1}` -/

/-- `U × (ℂP^{d+1} ∖ pt)` is homotopy equivalent to `U × ℂP^d`. -/
def punctHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥(punctUSet U d) (U × CP d) :=
  (prodSubtypeHomeo U
      ((punctOpen d : Opens (CPtop (d + 1)))
        : Set ↥(CPtop (d + 1)))).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl U).prodCongr (punctOpenHomotopyEquiv d))

/-- The intersection is `U × S^{2d+1}`. -/
def interHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥(interUSet U d) (U × Sphere (2 * d + 1)) :=
  (prodSubtypeHomeo U
      ((chartOpen d ⊓ punctOpen d : Opens (CPtop (d + 1)))
        : Set ↥(CPtop (d + 1)))).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl U).prodCongr (interSphereHomotopyEquiv d))

/-- The punctured identification commutes with the projection to `U`. -/
theorem punctHE_comp_prU :
    cmap (punctHomotopyEquiv U d).toFun
        ≫ (cmap ContinuousMap.fst : TopCat.of (U × CP d) ⟶ TopCat.of U)
      = cpPrSub U d (punctUSet U d) := by
  apply TopCat.Hom.ext
  ext p
  rfl

/-- The intersection identification commutes with the projection to `U`. -/
theorem interHE_comp_prU :
    cmap (interHomotopyEquiv U d).toFun ≫ knPrY U (2 * d + 1)
      = cpPrSub U d (interUSet U d) := by
  apply TopCat.Hom.ext
  ext p
  rfl

/-- Pulling back along the intersection identification is a linear isomorphism. -/
def interPullEquiv (k : ℕ) :
    Hmod2 (TopCat.of (U × Sphere (2 * d + 1))) k
      ≃ₗ[ZMod 2] Hmod2 (TopCat.of ↥(interUSet U d)) k :=
  pullEquivOfHomotopyEquiv (interHomotopyEquiv U d) k

/-- Pulling back along the punctured identification is a linear isomorphism. -/
def punctPullEquiv (k : ℕ) :
    Hmod2 (TopCat.of (U × CP d)) k ≃ₗ[ZMod 2] Hmod2 (TopCat.of ↥(punctUSet U d)) k :=
  pullEquivOfHomotopyEquiv (punctHomotopyEquiv U d) k

theorem pull_interHE_prU (k : ℕ) (c : Hmod2 (TopCat.of U) k) :
    pull (cmap (interHomotopyEquiv U d).toFun) k (pull (knPrY U (2 * d + 1)) k c)
      = pull (cpPrSub U d (interUSet U d)) k c := by
  rw [← pull_comp, interHE_comp_prU]

theorem pull_punctHE_prU (k : ℕ) (c : Hmod2 (TopCat.of U) k) :
    pull (cmap (punctHomotopyEquiv U d).toFun) k
        (pull (cmap ContinuousMap.fst : TopCat.of (U × CP d) ⟶ TopCat.of U) k c)
      = pull (cpPrSub U d (punctUSet U d)) k c := by
  rw [← pull_comp, punctHE_comp_prU]

end KnCP

end

end GroupApproximation.CharClass
