import GroupApproximation.Sofic.MFCamouflageRadical
import GroupApproximation.Sofic.MatricialStabilityInstances
import GroupApproximation.Sofic.UniversalFactorization
import GroupApproximation.Stability.MixedApproximation

/-!
# Split MF equivalences preserve point-norm matricial stability

Let `pi : G →* Q` admit a section `s : Q →* G`.  If precomposition with
`pi` is a bijection on representations into every norm-matrix corona, then
`G` is point-norm matricially stable exactly when `Q` is.

The forward implication is stability of retracts.  In the reverse direction,
the corona representation of an almost representation of `G` factors through
`pi`.  Equality in the corona says that the almost representation is
pointwise close to its restriction along `s ∘ pi`; stability of `Q` then
repairs that restriction on the same matrix spaces.
-/

namespace GroupApproximation
namespace SplitMFStability

open MatricialStabilityRadical MatricialStabilityInstances
open scoped Matrix.Norms.L2Operator

variable {G : Type} [Group G] {Q : Type} [Group Q]

/-- The corona representation induced by restriction is precomposition of
the original corona representation. -/
theorem coronaHom_comap (A : OpAlmostRepresentation G) (f : Q →* G) :
    (A.comap f).coronaHom = A.coronaHom.comp f := by
  ext q
  rfl

/-- Point-norm matricial stability descends to a retract. -/
theorem stable_of_retract (pi : G →* Q) (s : Q →* G)
    (hsplit : pi.comp s = MonoidHom.id Q)
    (hG : IsPointNormMatriciallyStable G) :
    IsPointNormMatriciallyStable Q := by
  intro A
  obtain ⟨sigma, hsigma⟩ := hG (A.comap pi)
  refine ⟨fun n ↦ (sigma n).comp s, fun q ↦ ?_⟩
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hsigma (s q) epsilon hepsilon
  refine ⟨N, fun n hn ↦ ?_⟩
  have hq : pi (s q) = q := by
    simpa using DFunLike.congr_fun hsplit q
  simpa only [OpAlmostRepresentation.comap_map, MonoidHom.comp_apply, hq]
    using hN n hn

/-- **Split corona equivalences preserve point-norm matricial stability.**
The hypothesis is deliberately stated at every positive sequence of finite
models.  It says exactly that `pi` erases no genuine asymptotic
finite-dimensional representation data. -/
theorem stable_iff_of_split_corona_equivalence
    (pi : G →* Q) (s : Q →* G)
    (hsplit : pi.comp s = MonoidHom.id Q)
    (hcorona : ∀ (X : ℕ → FiniteModel),
      (∀ n, 0 < Fintype.card (X n)) →
        Function.Bijective
          (fun psi : Q →* NormMatrixCoronaUnitary X ↦ psi.comp pi)) :
    IsPointNormMatriciallyStable G ↔
      IsPointNormMatriciallyStable Q := by
  constructor
  · exact stable_of_retract pi s hsplit
  · intro hQ A
    obtain ⟨Psi, hPsi⟩ :=
      (hcorona A.model A.modelNonempty).2 A.coronaHom
    obtain ⟨rho, hrho⟩ := hQ (A.comap s)
    refine ⟨fun n ↦ (rho n).comp pi, fun g ↦ ?_⟩
    intro epsilon hepsilon
    have hclass :
        (QuotientGroup.mk (fun n ↦ A.map n g) :
            NormMatrixCoronaUnitary A.model) =
          QuotientGroup.mk (fun n ↦ A.map n (s (pi g))) := by
      change A.coronaHom g = A.coronaHom (s (pi g))
      have hg := DFunLike.congr_fun hPsi g
      have hspg := DFunLike.congr_fun hPsi (s (pi g))
      have hsplitAt : pi (s (pi g)) = pi g := by
        simpa using DFunLike.congr_fun hsplit (pi g)
      rw [MonoidHom.comp_apply] at hg hspg
      exact hg.symm.trans ((congrArg Psi hsplitAt).symm.trans hspg)
    have hnull :
        (fun n ↦ A.map n g)⁻¹ * (fun n ↦ A.map n (s (pi g))) ∈
          nullCofiniteOpSubgroup A.model :=
      QuotientGroup.eq.mp hclass
    have hcloseEventually := hnull (epsilon / 2) (by linarith)
    rw [Nat.cofinite_eq_atTop] at hcloseEventually
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hcloseEventually
    obtain ⟨N₂, hN₂⟩ := hrho (pi g) (epsilon / 2) (by linarith)
    refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
    have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
    have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
    have hfirst :
        ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) -
          A.map n (s (pi g))‖ ≤ epsilon / 2 := by
      have h := hN₁ n hn₁
      change opLength (A.model n)
        ((A.map n g)⁻¹ * A.map n (s (pi g))) < epsilon / 2 at h
      rw [opLength_inv_mul] at h
      simpa only [norm_sub_rev] using h.le
    have hsecond :
        ‖(A.map n (s (pi g)) : Matrix (A.model n) (A.model n) ℂ) -
          rho n (pi g)‖ ≤ epsilon / 2 := by
      simpa only [OpAlmostRepresentation.comap_map] using hN₂ n hn₂
    calc
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) -
          ((rho n).comp pi) g‖ ≤
        ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) -
            A.map n (s (pi g))‖ +
          ‖(A.map n (s (pi g)) : Matrix (A.model n) (A.model n) ℂ) -
            rho n (pi g)‖ :=
        norm_sub_le_add_norm_sub _ _ _
      _ ≤ epsilon / 2 + epsilon / 2 := add_le_add hfirst hsecond
      _ = epsilon := by ring

end SplitMFStability

namespace MFCamouflage

open MatricialStabilityRadical

/-- **Camouflage surgery preserves point-norm matricial stability exactly.**
Full MF invisibility of the black-hole vertex gives the required corona
equivalence, while `visible` is a section of `projection`. -/
theorem isPointNormMatriciallyStable_camouflage_iff
    {B Q : Type} [Group B] [Group Q] (d : B)
    (hfull : actualCoronaMFResidual B = ⊤) :
    IsPointNormMatriciallyStable (Camouflage d Q) ↔
      IsPointNormMatriciallyStable Q := by
  apply SplitMFStability.stable_iff_of_split_corona_equivalence
    (projection d Q) (visible d Q) (projection_comp_visible d Q)
  intro X hX
  have hker : (projection d Q).ker ≤ coronaMFResidual (Camouflage d Q) := by
    rw [← actualCoronaMFResidual_eq_coronaMFResidual]
    exact projection_ker_le_actualCoronaMFResidual d Q hfull
  exact UniversalFactorization.corona_comp_bijective
    (projection d Q) (projection_surjective d Q) hker X hX

/-- Unconditional Hilbert-hotel specialization of stability preservation. -/
theorem Hotel.isPointNormMatriciallyStable_camouflage_iff
    (Q : Type) [Group Q] :
    IsPointNormMatriciallyStable (Hotel.Camouflage Q) ↔
      IsPointNormMatriciallyStable Q :=
  MFCamouflage.isPointNormMatriciallyStable_camouflage_iff
    (B := Hotel.BlackHole) (Q := Q) Hotel.sourceDefect
      Hotel.source_actualCoronaMFResidual_eq_top

end MFCamouflage
end GroupApproximation
