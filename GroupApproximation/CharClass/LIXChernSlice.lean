import GroupApproximation.CharClass.LIXChernValue
import GroupApproximation.CharClass.CohomologyLIXSliceBridge
import GroupApproximation.CharClass.ChernSliceNaturality

/-!
# The mod-2 Chern classes of a family on `N`, restricted to the slice

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`CharClass/ChernSliceNaturality.lean` proves naturality of the mod-2 Chern classes
along an arbitrary map of compact non-empty bases.  This file is its instance at
`lixN dd = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}` and `cc-cohom-api`'s `lixSlice`, the slice at a
point of the circle and a point of the sphere of unit vectors.

Nothing here is about the model: `lixSliceMap` is `lixSlice` presented as a
`C(baseY dd, _)`, which is the shape `Bundle.comap` eats, and `cmap_lixSliceMap`
says the two are the same map.  `pull_nSlice_lixIso` then carries this statement
into `KnTwo.ChernSliceNatural`, which is `cc-cohom-api`'s step, not this file's.

The rank hypothesis is the one `lixChern` branches on, so `lixChern_eq_of_rank`
takes the branch and the rest is `LH.chern_comap`.

## Main declarations

* `lixSliceMap` — the slice of `lixN` as a continuous map of the concrete bases.
* `cmap_lixSliceMap` — it is `cc-cohom-api`'s `lixSlice`.
* `pull_lixChern_lixSlice` — **naturality of `lixChern` along the slice**.

## Manuscript status

Machinery.  The first of the two facts about the Chern class that the slice
identification of Lemma 2 consumes, at the model the classes actually live on.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-- **The slice of `lixN`** as a continuous map of the concrete bases: `y ↦ (p₁, (q₅, y))`.
`Bundle.comap` restricts a family along a `C(_, _)`, not along a morphism of `TopCat`,
so the slice is needed in this shape as well as `cc-cohom-api`'s. -/
def lixSliceMap (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne) (q5 : ↥(unitVectors (Fin 3))) :
    C(baseY dd, ↥sphereOne × baseM dd) :=
  ⟨fun y => (p1, (q5, y)),
    continuous_const.prodMk (continuous_const.prodMk continuous_id)⟩

/-- It is `cc-cohom-api`'s slice; the two presentations agree on the nose. -/
theorem cmap_lixSliceMap (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q5 : ↥(unitVectors (Fin 3))) :
    cmap (lixSliceMap dd p1 q5) = lixSlice dd p1 q5 := rfl

/-- **Naturality of `lixChern` along the slice of `lixN`.**  For a family of
constant positive rank, the classes restricted to the slice are the classes of the
restricted family over `baseY dd`.

The rank hypothesis is exactly the branch condition of `lixChern`, so no
generality is lost: off that branch `lixChern` is `0` by fiat and there is nothing
to be natural about. -/
theorem pull_lixChern_lixSlice (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q5 : ↥(unitVectors (Fin 3))) (P : LixFamily dd) (hcont : Continuous P)
    (hproj : ∀ p, IsStarProjection (P p)) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : ∀ x, (⟨P, hcont, hproj⟩ :
      Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd)).rank x = s) (k : ℕ) :
    pull (lixSlice dd p1 q5) (2 * k) (lixChern dd P hcont hproj k)
      = LH.chernOf (comap (lixSliceMap dd p1 q5)
          (⟨P, hcont, hproj⟩ :
            Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))) s
          (fun y => hs (lixSliceMap dd p1 q5 y)) hs1 k := by
  have hcomap := LH.chern_comap (lixSliceMap dd p1 q5)
    (⟨P, hcont, hproj⟩ : Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd)) s hs hs1 k
  have h2 : LH.chernOf (comap (lixSliceMap dd p1 q5)
        (⟨P, hcont, hproj⟩ :
          Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))) s
        (fun y => hs (lixSliceMap dd p1 q5 y)) hs1 k
      = pull (lixSlice dd p1 q5) (2 * k)
          (TotalH.component (TopCat.of (↥sphereOne × baseM dd)) (2 * k)
            ((LHCast.lerayHirschData_of_graded
              (LH.lerayHirschGraded_compact
                (⟨P, hcont, hproj⟩ :
                  Bundle (↥sphereOne × baseM dd) (VIdx dd ⊕ VIdx dd))
                s hs hs1)).chern k)) := by
    simp only [LH.chernOf]
    rw [hcomap, Wu.totalH_component_map, cmap_lixSliceMap]
    rfl
  rw [lixChern_eq_of_rank P hcont hproj s hs1 hs k]
  exact h2.symm

end

end CharClass
end GroupApproximation
