import GroupApproximation.CharClass.ThomTopLineLIX
import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.Meta.AxiomGuard

/-!
# The top mod-2 cohomology of the rank-`n` LIX base is a line

Lane `lix-oddside-n` (leaf (1) of the Step C half, `absLine`).

`CharClass/ThomTopLineLIX.lean` proves `H^{2(∑ⱼ dⱼ) + 6}(S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}; F₂) ≃ F₂` by
induction over the projective factors, over a model homeomorphism for `S⁵`.  At rank `n` the
same induction runs over `baseNilHomeo n` / `baseSnocHomeo n` (`CharClass/LIXKGenPunctured.lean`),
and the model homeomorphism is `KGen.unitVectorsHomeo n : ↥(unitVectors (Fin (n+1))) ≃ₜ S^{2n+1}`
(`CharClass/LIXKGenSphere.lean`), so nothing is assumed.

## Main declarations

* `KGen.hasTopLine_circleTimesSphere n` — `H^{2n+2}(S¹ × S^{2n+1}; F₂) ≃ F₂`.
* `KGen.hasTopLine_lixBase n` — the induction over the projective factors.
* `KGen.absEquiv_lixN n dd hdd` — **`H^{2r}(N; F₂) ≃ F₂` at rank `n`**, the `absLine` binder of
  `KGen.lixK_topClass_ne_zero_two`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59

namespace GroupApproximation.CharClass

namespace KGen

noncomputable section

set_option linter.unusedSectionVars false

/-- **`H^{2n+2}(S¹ × S^{2n+1}; F₂) ≃ F₂`**, with the sphere model discharged. -/
theorem hasTopLine_circleTimesSphere (n : ℕ) :
    HasTopLine (↥sphereOne × ↥(unitVectors (Fin (n + 1)))) (2 * n + 2) := by
  have h : HasTopLine (↥sphereOne × Sphere (2 * n + 1)) (1 + (2 * n + 1)) :=
    hasTopLine_prod_sphere circleTopLineStep ↥sphereOne 1 hasTopLine_sphereOne (2 * n + 1)
      (by omega)
  have hdeg : 1 + (2 * n + 1) = 2 * n + 2 := by omega
  rw [hdeg] at h
  exact h.congr ((Homeomorph.refl ↥sphereOne).prodCongr (unitVectorsHomeo n).symm)

/-- **The top line at the rank-`n` LIX base**, by induction on the projective factors. -/
theorem hasTopLine_lixBase (n : ℕ) :
    ∀ (ℓ : ℕ) (dd : Fin ℓ → ℕ), (∀ j, 0 < dd j) →
      HasTopLine (↥sphereOne × Gen.baseM n dd) (2 * (∑ j, dd j) + (2 * n + 2)) := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro dd _
      have hdeg : 2 * (∑ j : Fin 0, dd j) + (2 * n + 2) = 2 * n + 2 := by simp
      rw [hdeg]
      exact (hasTopLine_circleTimesSphere n).congr (baseNilHomeo n dd).symm
  | succ ℓ ih =>
      intro dd hdd
      have hdeg : 2 * (∑ j : Fin (ℓ + 1), dd j) + (2 * n + 2)
          = (2 * (∑ j : Fin ℓ, dd j.castSucc) + (2 * n + 2)) + 2 * dd (Fin.last ℓ) := by
        rw [Fin.sum_univ_castSucc dd]
        ring
      rw [hdeg]
      refine HasTopLine.congr ?_ (baseSnocHomeo n dd).symm
      exact hasTopLine_prod_CP circleTopLineStep _ _
        (ih (fun j => dd j.castSucc) (fun j => hdd j.castSucc))
        (dd (Fin.last ℓ)) (hdd (Fin.last ℓ))

/-- **`H^{2r}(N; F₂) ≃ F₂` at rank `n`**: the `absLine` binder of the `k`-zero Step C. -/
theorem absEquiv_lixN (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) :
    Nonempty (cohomologyZMod2 (lixN n dd) (2 * lixRank n dd) ≃ₗ[ZMod 2] ZMod 2) := by
  have h := hasTopLine_lixBase n ℓ dd hdd
  have hdeg : 2 * (∑ j, dd j) + (2 * n + 2) = 2 * lixRank n dd := by
    rw [lixRank]
    ring
  rw [hdeg] at h
  exact h.line

end

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.hasTopLine_circleTimesSphere
#audit_axioms KGen.absEquiv_lixN

end GroupApproximation.CharClass
