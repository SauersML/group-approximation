import GroupApproximation.CharClass.MayerVietorisPullAmbient

/-!
# Naturality of the Mayer–Vietoris restrictions in a map of covered spaces

For `f : Y ⟶ X` and a two-element open cover `U ⊔ V = ⊤` of `X`, the preimages cover
`Y`, and the four Mayer–Vietoris restrictions commute with `f`.  This is what
`cc-projective`'s Leray–Hirsch ladder needs for the bundle projection `P(E) → X`.

All four are now mechanical, because `MayerVietorisPull.lean` and
`MayerVietorisPullAmbient.lean` identify every Mayer–Vietoris restriction with an
honest `cohPullback`: each square becomes `pull_comp` applied to the two ways round a
commuting square of *spaces*, and each of those commutes by `rfl` because both
composites send a point to its image under `f`.

The fifth square, for the connecting map, is **not** here: it needs a cochain-level
description of `δ`, which is `cc-cohom-api`'s `mvDelta_spec`, and by the lead's split it
is derived there rather than here.

## Main results

* `opensComap_sup_eq_top` — the preimage cover is a cover.
* `opensRestrict`, `interRestrict` — `f` restricted to a piece and to the intersection.
* `mvResU_naturality`, `mvResV_naturality`, `mvResWU_naturality`, `mvResWV_naturality`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X Y : TopCat.{0}}

/-- The preimage of an open along a map of spaces. -/
abbrev opensComap (f : Y ⟶ X) (U : Opens X) : Opens Y := Opens.comap f.hom U

/-- **The preimage of a cover is a cover.** -/
theorem opensComap_sup_eq_top (f : Y ⟶ X) {U V : Opens X} (hUV : U ⊔ V = ⊤) :
    opensComap f U ⊔ opensComap f V = ⊤ := by
  rw [← map_sup, hUV, map_top]

/-- `f` restricted to the preimage of an open. -/
def opensRestrict (f : Y ⟶ X) (U : Opens X) :
    TopCat.of ((opensComap f U : Opens Y) : Set Y) ⟶ TopCat.of ((U : Opens X) : Set X) :=
  TopCat.ofHom ⟨fun y => ⟨f.hom (y : Y), y.2⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- `f` restricted to the preimage of the intersection. -/
def interRestrict (f : Y ⟶ X) (U V : Opens X) :
    TopCat.of ((((opensComap f U : Opens Y) : Set Y)
        ∩ ((opensComap f V : Opens Y) : Set Y) : Set Y))
      ⟶ TopCat.of ((((U : Opens X) : Set X) ∩ ((V : Opens X) : Set X) : Set X)) :=
  TopCat.ofHom ⟨fun y => ⟨f.hom (y : Y), y.2.1, y.2.2⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem opensRestrict_comp_sInclusion (f : Y ⟶ X) (U : Opens X) :
    opensRestrict f U ≫ sInclusion ((U : Opens X) : Set X)
      = sInclusion ((opensComap f U : Opens Y) : Set Y) ≫ f := rfl

theorem interRestrict_comp_subInclusionLeft (f : Y ⟶ X) (U V : Opens X) :
    interRestrict f U V ≫ subInclusion (Set.inter_subset_left
        (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))
      = subInclusion (Set.inter_subset_left
          (s := ((opensComap f U : Opens Y) : Set Y))
          (t := ((opensComap f V : Opens Y) : Set Y))) ≫ opensRestrict f U := rfl

theorem interRestrict_comp_subInclusionRight (f : Y ⟶ X) (U V : Opens X) :
    interRestrict f U V ≫ subInclusion (Set.inter_subset_right
        (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))
      = subInclusion (Set.inter_subset_right
          (s := ((opensComap f U : Opens Y) : Set Y))
          (t := ((opensComap f V : Opens Y) : Set Y))) ≫ opensRestrict f V := rfl

/-- **Naturality of the restriction to the first piece.** -/
theorem mvResU_naturality (f : Y ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (x : Hmod2 X n) :
    (mvResU (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull f n x)
      = pull (opensRestrict f U) n ((mvResU U V hUV n).hom x) := by
  rw [mvResU_eq_pull, mvResU_eq_pull]
  show pull (sInclusion ((opensComap f U : Opens Y) : Set Y)) n (pull f n x)
      = pull (opensRestrict f U) n (pull (sInclusion ((U : Opens X) : Set X)) n x)
  rw [← pull_comp, ← pull_comp, opensRestrict_comp_sInclusion]

/-- **Naturality of the restriction to the second piece.** -/
theorem mvResV_naturality (f : Y ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (x : Hmod2 X n) :
    (mvResV (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull f n x)
      = pull (opensRestrict f V) n ((mvResV U V hUV n).hom x) := by
  rw [mvResV_eq_pull, mvResV_eq_pull]
  show pull (sInclusion ((opensComap f V : Opens Y) : Set Y)) n (pull f n x)
      = pull (opensRestrict f V) n (pull (sInclusion ((V : Opens X) : Set X)) n x)
  rw [← pull_comp, ← pull_comp, opensRestrict_comp_sInclusion]

/-- **Naturality of the restriction of the first piece to the intersection.** -/
theorem mvResWU_naturality (f : Y ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (a : Hmod2 (mvU U) n) :
    (mvResWU (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull (opensRestrict f U) n a)
      = pull (interRestrict f U V) n ((mvResWU U V hUV n).hom a) := by
  rw [mvResWU_eq_pull, mvResWU_eq_pull]
  show pull (subInclusion (Set.inter_subset_left
        (s := ((opensComap f U : Opens Y) : Set Y))
        (t := ((opensComap f V : Opens Y) : Set Y)))) n (pull (opensRestrict f U) n a)
      = pull (interRestrict f U V) n
          (pull (subInclusion (Set.inter_subset_left
            (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))) n a)
  rw [← pull_comp, ← pull_comp, interRestrict_comp_subInclusionLeft]

/-- **Naturality of the restriction of the second piece to the intersection.** -/
theorem mvResWV_naturality (f : Y ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (b : Hmod2 (mvU V) n) :
    (mvResWV (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull (opensRestrict f V) n b)
      = pull (interRestrict f U V) n ((mvResWV U V hUV n).hom b) := by
  rw [mvResWV_eq_pull, mvResWV_eq_pull]
  show pull (subInclusion (Set.inter_subset_right
        (s := ((opensComap f U : Opens Y) : Set Y))
        (t := ((opensComap f V : Opens Y) : Set Y)))) n (pull (opensRestrict f V) n b)
      = pull (interRestrict f U V) n
          (pull (subInclusion (Set.inter_subset_right
            (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))) n b)
  rw [← pull_comp, ← pull_comp, interRestrict_comp_subInclusionRight]

end

end GroupApproximation.CharClass
