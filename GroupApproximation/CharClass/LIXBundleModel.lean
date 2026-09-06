import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.CharClass.BundleBasic

/-!
# The mapping torus as a bundle

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3, deliverable 1).

Until now `mappingTorus` existed only as a continuous family of matrices; the word
"bundle" appeared in its docstrings and nowhere in its types.  `cc-thom`'s residual list
for Step C ends at "once the bundle's trivialisation over the chart is available", and
that phrase presupposes an object nobody had built: there is no `Bundle` over
`↥sphereOne × baseM dd` anywhere in the tree, and no `relCohomology` at `lixN`.

This file supplies the first of the three missing steps, which is the one that belongs to
this lane: the mapping torus **as a `Bundle`**.  Both of its fields are theorems this lane
already had, so this is an assembly rather than a construction.

What still does not exist, and is nobody's assigned work at the time of writing:

* the projectivised sum `P(E ⊕ 1)` and its zero locus, giving the relative group;
* the section as a **map of pairs**, which is the morphism `cc-thom`'s residual is about.

## The rank

`rank_lixBundle` records `rank W_g = rank V = (∑ⱼ dⱼ) + 3` at every point, which is
deliverable 1 of this lane's brief.  It is the trace computation of
`trace_mappingTorus` and `trace_Vmat` read through `Bundle.trace_eq_rank`, with no
spectral theorem.

## Main results

* `lixBundle` — the mapping torus of a corner unitary, as a `Bundle`.
* `rank_lixBundle` — its rank is `lixRank dd`, everywhere.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The bundle -/

/-- **The mapping torus `W_g`, as a bundle over `S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}`.**  The two fields
are `continuous_mappingTorus_lix` and `isStarProjection_mappingTorus_lix`. -/
def lixBundle (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd) where
  toFun := mappingTorus Vmat G circHoriz circHeight
  continuous_toFun := continuous_mappingTorus_lix hGc
  isStarProjection_toFun := isStarProjection_mappingTorus_lix hGu

@[simp] theorem coe_lixBundle (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ⇑(lixBundle G hGc hGu) = mappingTorus Vmat G circHoriz circHeight := rfl

/-! ## 2. The rank -/

/-- **`rank W_g = rank V`, everywhere.**  Deliverable 1 of this lane's brief, now stated
about an actual bundle.  The mapping torus has the trace of `V` at every point, and `V` has
trace `(∑ⱼ dⱼ) + 3`, which is `lixRank dd`. -/
theorem rank_lixBundle (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (p : ↥sphereOne × baseM dd) :
    (lixBundle G hGc hGu).rank p = lixRank dd := by
  have htr : Matrix.trace ((lixBundle G hGc hGu) p) = ((lixRank dd : ℕ) : ℂ) := by
    show Matrix.trace (mappingTorus Vmat G circHoriz circHeight p) = _
    rw [trace_mappingTorus, trace_Vmat]
    rfl
  have h := Bundle.trace_eq_rank (lixBundle G hGc hGu) p
  rw [htr] at h
  exact_mod_cast h.symm

end GroupApproximation.CharClass
