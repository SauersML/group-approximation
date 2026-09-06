import GroupApproximation.CharClass.ThomTopLineCircle
import GroupApproximation.CharClass.LemmaTwoTopClass

/-!
# The top line of the LIX base

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomTopLine.lean` and `ThomTopLineCircle.lean` prove that a left-nested product
of spheres and complex projective spaces has a one-dimensional mod-2 cohomology
in its top degree.  This file runs that induction at

```text
N = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ},      top degree  2(∑ⱼ dⱼ) + 6,
```

which is `absEquiv`, the eighth argument of
`topChernClass_ne_zero_of_chain` and the last one this lane owns.

The re-nesting is `cc-lix-odd`'s `baseNilHomeo` / `baseSnocHomeo`, the same pair
that carried `puncturedAcyclic_lixBase`: the projective factors are peeled from
the **last** index, so every second factor of the induction is a single `ℂP^d`.

## The one input, and where it is discharged

`unitVectors (Fin 3)` is `{x : Fin 3 → ℂ | ∑ᵢ ‖xᵢ‖² = 1}`, a subset of the plain
function type, while `Sphere 5` is the unit sphere of
`EuclideanSpace ℝ (Fin 6) = WithLp 2 (Fin 6 → ℝ)`, a one-field structure over a
*real* six-coordinate space.  The two are **not** definitionally equal, so the
statements below take the model homeomorphism `↥(unitVectors (Fin 3)) ≃ₜ S⁵` as a
hypothesis and it is genuine content: `cc-lix-odd`'s
`CharClass/LIXStepESphereModel.lean` pays the norm identity, the two round trips
and continuity across the structure seam.

It is **discharged**, not outstanding.  `unitVectorsThreeHomeo` supplies it, and
`LemmaTwoStepCAbsEquiv.unitVectorsThreeHomeoSphere` retypes it at `Sphere 5` with
no transport — that last step *is* free, because `Sphere` is a reducible
abbreviation and `5 + 1` and `6` are the same literal, but only that step is.

Nothing else is assumed: the circle step is discharged in
`ThomTopLineCircle.lean`.

## Main declarations

* `hasTopLine_sphereOne` — the circle factor, on the nose.
* `hasTopLine_circleTimesFive` — `H^6(S¹ × S⁵; F₂) ≃ F₂`.
* `hasTopLine_lixBase` — the induction over the projective factors.
* `absEquiv_lixN` — **hypothesis 8 of Step C**, in the shape `LemmaTwoStepC` asks for.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59

namespace GroupApproximation.CharClass

noncomputable section

set_option linter.unusedSectionVars false

/-! ## 1. The two sphere factors -/

/-- **The circle factor, with no transport.**  `sphereOne` *is* the unit sphere of
`EuclideanSpace ℝ (Fin 2)`, so the sphere base case applies on the nose. -/
theorem hasTopLine_sphereOne : HasTopLine ↥sphereOne 1 :=
  hasTopLine_sphere 1 (by norm_num)

/-- **`H^6(S¹ × S⁵; F₂) ≃ F₂`**, modulo the model homeomorphism for `S⁵`. -/
theorem hasTopLine_circleTimesFive (e : ↥(unitVectors (Fin 3)) ≃ₜ Sphere 5) :
    HasTopLine (↥sphereOne × ↥(unitVectors (Fin 3))) 6 :=
  (hasTopLine_prod_sphere circleTopLineStep ↥sphereOne 1 hasTopLine_sphereOne 5
    (by norm_num)).congr ((Homeomorph.refl ↥sphereOne).prodCongr e.symm)

/-! ## 2. The induction over the projective factors -/

/-- **The top line at the LIX base.**  Induction on the number of projective
factors, peeling the last one with `baseSnocHomeo` and transporting with
`HasTopLine.congr`; the base case is `baseNilHomeo` against the two sphere
factors.  The circle step is already discharged, so this is unconditional given
the model homeomorphism. -/
theorem hasTopLine_lixBase (hbase : HasTopLine (↥sphereOne × ↥(unitVectors (Fin 3))) 6) :
    ∀ (ℓ : ℕ) (dd : Fin ℓ → ℕ), (∀ j, 0 < dd j) →
      HasTopLine (↥sphereOne × baseM dd) (2 * (∑ j, dd j) + 6) := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro dd _
      have hdeg : 2 * (∑ j : Fin 0, dd j) + 6 = 6 := by simp
      rw [hdeg]
      exact hbase.congr (baseNilHomeo dd).symm
  | succ ℓ ih =>
      intro dd hdd
      have hdeg : 2 * (∑ j : Fin (ℓ + 1), dd j) + 6
          = (2 * (∑ j : Fin ℓ, dd j.castSucc) + 6) + 2 * dd (Fin.last ℓ) := by
        rw [Fin.sum_univ_castSucc dd]
        ring
      rw [hdeg]
      refine HasTopLine.congr ?_ (baseSnocHomeo dd).symm
      exact hasTopLine_prod_CP circleTopLineStep _ _
        (ih (fun j => dd j.castSucc) (fun j => hdd j.castSucc))
        (dd (Fin.last ℓ)) (hdd (Fin.last ℓ))

/-! ## 3. Hypothesis 8 of Step C -/

/-- **The top line at `N`, in the degree index `LemmaTwoStepC` uses.** -/
theorem hasTopLine_lixN (e : ↥(unitVectors (Fin 3)) ≃ₜ Sphere 5)
    {ℓ : ℕ} (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) :
    HasTopLine (↥sphereOne × baseM dd) (lixTopDegree dd) :=
  hasTopLine_lixBase (hasTopLine_circleTimesFive e) ℓ dd hdd

/-- **Hypothesis 8 of Step C**: the top mod-2 cohomology of `N` is a line.  This is
the `absEquiv` field of `LemmaTwoStepC`'s data, modulo the one model
homeomorphism `cc-lix-odd` owes. -/
theorem absEquiv_lixN (e : ↥(unitVectors (Fin 3)) ≃ₜ Sphere 5)
    {ℓ : ℕ} (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) :
    Nonempty (cohomologyZMod2 (lixN dd) (2 * lixRank dd) ≃ₗ[ZMod 2] ZMod 2) := by
  have h := hasTopLine_lixN e dd hdd
  rw [lixTopDegree_eq_two_mul_lixRank dd] at h
  exact h.line

end

end GroupApproximation.CharClass
