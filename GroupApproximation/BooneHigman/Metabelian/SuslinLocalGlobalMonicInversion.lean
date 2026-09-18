import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalMonicMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Monic inversion for `E_N`, `N ≥ 3`: reduction to local rings

Lane `bh-sus-02`.  *Normalized monic inversion* (Suslin's `K₁`-analogue of Horrocks'
theorem): for a commutative ring `A`, `N > 2`, a monic `f ∈ A[X]` and `σ ∈ GL_N(A[X])` with
`σ(0) = 1`, if the image of `σ` in `GL_N(A[X]_f)` lies in `E_N(A[X]_f)`, then
`σ ∈ E_N(A[X])`.

`suslinLG_monicInversion_of_local` proves this for **every** commutative ring from the
**local** case `suslinLG_LocalMonicInversionStatement`, by the unconditional local-global
principle `suslinLG_localGlobal`: for each maximal `𝔪` the base change `σ_𝔪` is still
normalized (`suslinLG_zero_map`), `f_𝔪` is still monic (`Polynomial.Monic.map`) and `σ_𝔪` is
still `f_𝔪`-locally elementary (`suslinLG_away_mem_map`).

## The residual

`suslinLG_LocalMonicInversionStatement` is normalized monic inversion **over local rings
only**.  It is

* *true*: it is the local instance of Suslin's monic inversion theorem (`α ∈ GL_N(A[X])`,
  `α_f ∈ E_N(A[X]_f)`, `f` monic, `N ≥ 3` gives `α ∈ E_N(A[X]) · GL_N(A)`; with `α(0) = 1`
  the constant factor is `ε(0)⁻¹ ∈ E_N(A)`);
* *strictly smaller in proof content* than monic inversion over all rings: the whole
  local-global patching (Quillen ideal, dilation, clearing denominators) is proved here, and
  only the local case remains (logically it is equivalent to the global normalized form
  modulo `suslinLG_monicInversion_of_local`, and a special case of it);
* *not* a restatement of `suslinZLocal_BadStatement` (S1): it hypothesizes `f`-local
  elementarity for a monic `f` and concludes nothing about `ℤ`-local or congruence data.

The normalization `σ(0) = 1` is essential to the formulation used here: the unnormalized
claim "`σ_f ∈ E_N(A[X]_f)` implies `σ ∈ E_N(A[X])`" would in particular require
`GL_N(A) ∩ E_N(A[X]_f) ⊆ E_N(A)`, which is not addressed.  Also, the naive `ℙ¹` splitting
`E_N(A[X]_{Xf}) = E_N(A[X]) · E_N(A[X⁻¹]_g)` is false (`diag(X, X⁻¹, 1, …)`), so no
Karoubi-style splitting is used or assumed.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

universe u

/-- **Residual: normalized monic inversion over local rings.**  For a local ring `R`, `N > 2`,
a monic `f ∈ R[X]` and `σ ∈ GL_N(R[X])` with `σ(0) = 1`: if `σ_f ∈ E_N(R[X]_f)` then
`σ ∈ E_N(R[X])`.  True (local case of Suslin's monic inversion); see the module docstring. -/
def suslinLG_LocalMonicInversionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (N : ℕ), 2 < N →
    ∀ (σ : Matrix.GeneralLinearGroup (Fin N) (Polynomial R)) (f : Polynomial R), f.Monic →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := R)) σ = 1 →
      elementaryMatrixUnitMap (ι := Fin N)
          (algebraMap (Polynomial R) (Localization.Away f)) σ ∈
        elementaryGroup (Fin N) (Localization.Away f) →
      σ ∈ elementaryGroup (Fin N) (Polynomial R)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLG_LocalMonicInversionStatement

/-- **Normalized monic inversion for every commutative ring**, from the local case. -/
theorem suslinLG_monicInversion_of_local {A : Type u} [CommRing A] {N : ℕ}
    (hL : suslinLG_LocalMonicInversionStatement.{u}) (hN : 2 < N)
    (σ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) (f : Polynomial A) (hf : f.Monic)
    (h0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) σ = 1)
    (hσ : elementaryMatrixUnitMap (ι := Fin N)
        (algebraMap (Polynomial A) (Localization.Away f)) σ ∈
      elementaryGroup (Fin N) (Localization.Away f)) :
    σ ∈ elementaryGroup (Fin N) (Polynomial A) := by
  refine suslinLG_localGlobal hN σ h0 fun 𝔪 _ ↦ ?_
  have hfm : (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪)) f).Monic := by
    rw [Polynomial.coe_mapRingHom]
    exact hf.map _
  exact hL (Localization.AtPrime 𝔪) N hN
    (elementaryMatrixUnitMap (ι := Fin N)
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ)
    (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪)) f) hfm
    (suslinLG_zero_map _ σ h0) (suslinLG_away_mem_map _ f σ hσ)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLG_monicInversion_of_local

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
