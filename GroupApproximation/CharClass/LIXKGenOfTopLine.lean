import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.CharClass.ThomTopLineOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The top cohomology of the rank-`n` LIX base is a line, over a field

Lane `lix-powers` (odd-`p` twins of lane `lix-oddside-n`'s rank-`n` Step C).

`CharClass/LIXKGenTopLine.lean` proves `H^{2r}(N; F₂) ≃ F₂` by induction on the projective
factors.  The same induction runs over any field `K` with lane `lix-thom`'s `ThomTopLineOf`:
`hasTopLineOf_sphere` for the circle, `hasTopLineOf_prod_sphere` for `S^{2n+1}`, and
`hasTopLineOf_prod_CP` for each `ℂP^{d_j}`, transported along `KGen.baseNilHomeo` and
`KGen.baseSnocHomeo`.

## Main declarations

* `KGen.hasTopLineOf_circleTimesSphere K n`.
* `KGen.hasTopLineOf_lixBase K n ℓ dd hdd`.
* `KGen.absEquiv_lixNOf K n dd hdd` — **`H^{2r}(N; K) ≃ K` at rank `n`**, the `absLine` binder.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59

namespace GroupApproximation.CharClass

namespace KGen

noncomputable section

set_option linter.unusedSectionVars false

/-- **`H^{2n+2}(S¹ × S^{2n+1}; K) ≃ K`**, with the sphere model discharged. -/
theorem hasTopLineOf_circleTimesSphere (K : Type) [Field K] (n : ℕ) :
    HasTopLineOf K (↥sphereOne × ↥(unitVectors (Fin (n + 1)))) (2 * n + 2) := by
  have hS : HasTopLineOf K ↥sphereOne 1 := hasTopLineOf_sphere K 1 le_rfl
  have h : HasTopLineOf K (↥sphereOne × Sphere (2 * n + 1)) (1 + (2 * n + 1)) :=
    hasTopLineOf_prod_sphere K ↥sphereOne 1 hS (2 * n + 1) (by omega)
  have hdeg : 1 + (2 * n + 1) = 2 * n + 2 := by omega
  rw [hdeg] at h
  exact h.congr ((Homeomorph.refl ↥sphereOne).prodCongr (unitVectorsHomeo n).symm)

/-- **The top line at the rank-`n` LIX base over `K`**, by induction on the projective
factors. -/
theorem hasTopLineOf_lixBase (K : Type) [Field K] (n : ℕ) :
    ∀ (ℓ : ℕ) (dd : Fin ℓ → ℕ), (∀ j, 0 < dd j) →
      HasTopLineOf K (↥sphereOne × Gen.baseM n dd) (2 * (∑ j, dd j) + (2 * n + 2)) := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro dd _
      have hdeg : 2 * (∑ j : Fin 0, dd j) + (2 * n + 2) = 2 * n + 2 := by simp
      rw [hdeg]
      exact (hasTopLineOf_circleTimesSphere K n).congr (baseNilHomeo n dd).symm
  | succ ℓ ih =>
      intro dd hdd
      have hdeg : 2 * (∑ j : Fin (ℓ + 1), dd j) + (2 * n + 2)
          = (2 * (∑ j : Fin ℓ, dd j.castSucc) + (2 * n + 2)) + 2 * dd (Fin.last ℓ) := by
        rw [Fin.sum_univ_castSucc dd]
        ring
      rw [hdeg]
      refine HasTopLineOf.congr ?_ (baseSnocHomeo n dd).symm
      exact hasTopLineOf_prod_CP K _ _
        (ih (fun j => dd j.castSucc) (fun j => hdd j.castSucc))
        (dd (Fin.last ℓ)) (hdd (Fin.last ℓ))

/-- **`H^{2r}(N; K) ≃ K` at rank `n`**: the `absLine` binder of the `k`-zero Step C over `K`. -/
theorem absEquiv_lixNOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (hdd : ∀ j, 0 < dd j) :
    Nonempty (Hmod K (lixN n dd) (2 * lixRank n dd) ≃ₗ[K] K) := by
  have h := hasTopLineOf_lixBase K n ℓ dd hdd
  have hdeg : 2 * (∑ j, dd j) + (2 * n + 2) = 2 * lixRank n dd := by
    rw [lixRank]
    ring
  rw [hdeg] at h
  exact h.line

end

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.hasTopLineOf_circleTimesSphere
#audit_axioms KGen.absEquiv_lixNOf

end GroupApproximation.CharClass
