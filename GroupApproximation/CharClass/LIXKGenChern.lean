import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.CharClass.LIXChernValue
import GroupApproximation.Meta.AxiomGuard

/-!
# The mod-2 Chern classes on the rank-`n` LIX base

Lane `lix-oddside-n` (leaf (5) of the Step C half, and the `γfun` adapter).

`CharClass/LIXChern.lean` defines `lixChern dd`, the degreewise mod-2 Chern classes of a
projection-valued family on `S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}`, through `cc-projective`'s compact-base
Leray–Hirsch theorem; `LemmaTwoTopClass.lixChernOf` makes it total in the ring `TotalH`, and
`LIXChernValue` records that the branch is taken on a mapping torus.  Nothing in those
constructions uses the rank of the sphere factor except through the base, so this file states
them over `lixN n dd = S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}` at every rank.

## Main declarations

* `KGen.LixFamily n dd`, `KGen.LixChernDeg n dd`.
* `KGen.lixChern n dd` — **the degreewise Chern classes at rank `n`**, total.
* `KGen.lixChern_eq_of_rank`, `KGen.lixChern_mappingTorus` — the branch is taken.
* `KGen.lixChernOf n chern`, `KGen.lixChernOf_mappingTorus` — the classes in `TotalH`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace KGen

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The base instances at rank `n` -/

/-- The Hermitian sphere `S^{2n+1}` is compact.  At `n = 2` this duplicates
`unitVectorsThree.instCompactSpace`, which is harmless for a `Prop`-valued class. -/
instance instCompactSpaceUnitVectors (n : ℕ) : CompactSpace ↥(unitVectors (Fin (n + 1))) :=
  isCompact_iff_compactSpace.mp (isCompact_unitVectors (Fin (n + 1)))

instance instNonemptyUnitVectors (n : ℕ) : Nonempty ↥(unitVectors (Fin (n + 1))) :=
  ⟨negEZero n⟩

theorem one_le_lixRank (n : ℕ) (dd : Fin ℓ → ℕ) : 1 ≤ lixRank n dd := by
  rw [lixRank]
  omega

/-! ## 2. The classes -/

/-- A family of matrices on `N = S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`. -/
abbrev LixFamily (n : ℕ) (dd : Fin ℓ → ℕ) : Type :=
  ↥sphereOne × Gen.baseM n dd →
    Matrix (Gen.VIdx n dd ⊕ Gen.VIdx n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd) ℂ

/-- A degreewise mod-2 Chern class assignment for projection-valued families on `N`. -/
abbrev LixChernDeg (n : ℕ) (dd : Fin ℓ → ℕ) : Type :=
  ∀ P : LixFamily n dd, Continuous P → (∀ p, IsStarProjection (P p)) →
    ∀ k : ℕ, Hmod2 (lixN n dd) (2 * k)

open scoped Classical in
/-- **The degreewise mod-2 Chern classes at rank `n`.**  Total: zero off the families of
constant positive rank. -/
def lixChern (n : ℕ) (dd : Fin ℓ → ℕ) : LixChernDeg n dd :=
  fun P hcont hproj k =>
    if h : ∃ s : ℕ, 1 ≤ s ∧ ∀ x, (⟨P, hcont, hproj⟩ : Bundle _ _).rank x = s then
      TotalH.component (lixN n dd) (2 * k)
        ((LHCast.lerayHirschData_of_graded
          (LH.lerayHirschGraded_compact (⟨P, hcont, hproj⟩ : Bundle _ _)
            h.choose h.choose_spec.2 h.choose_spec.1)).chern k)
    else 0

/-- **The branch is taken** whenever the bundle has constant positive rank. -/
theorem lixChern_eq_of_rank (n : ℕ) (P : LixFamily n dd) (hcont : Continuous P)
    (hproj : ∀ p, IsStarProjection (P p)) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : ∀ x, (⟨P, hcont, hproj⟩ : Bundle _ _).rank x = s) (k : ℕ) :
    lixChern n dd P hcont hproj k
      = TotalH.component (lixN n dd) (2 * k)
          ((LHCast.lerayHirschData_of_graded
            (LH.lerayHirschGraded_compact (⟨P, hcont, hproj⟩ : Bundle _ _) s hs hs1)).chern
              k) := by
  have hex : ∃ s : ℕ, 1 ≤ s ∧ ∀ x, (⟨P, hcont, hproj⟩ : Bundle _ _).rank x = s :=
    ⟨s, hs1, hs⟩
  have hchoose : hex.choose = s := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (↥sphereOne × Gen.baseM n dd))
    exact (hex.choose_spec.2 x).symm.trans (hs x)
  show dite _ _ _ = _
  rw [dif_pos hex]
  exact congrArg _ (chern_congr_rank _ hchoose
    hex.choose_spec.2 hex.choose_spec.1 hs hs1 k)

/-- **The branch is taken on a mapping torus**, at the rank `KGen.rank_lixBundle` computes. -/
theorem lixChern_mappingTorus (n : ℕ)
    (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hcont : Continuous (mappingTorus (Gen.Vmat n) G circHoriz circHeight))
    (hproj : ∀ p, IsStarProjection (mappingTorus (Gen.Vmat n) G circHoriz circHeight p))
    (k : ℕ) :
    lixChern n dd (mappingTorus (Gen.Vmat n) G circHoriz circHeight) hcont hproj k
      = TotalH.component (lixN n dd) (2 * k)
          ((LHCast.lerayHirschData_of_graded
            (LH.lerayHirschGraded_compact
              (⟨mappingTorus (Gen.Vmat n) G circHoriz circHeight, hcont, hproj⟩ : Bundle _ _)
              (lixRank n dd) (fun x => rank_lixBundle n G hGc hGu x)
              (one_le_lixRank n dd))).chern k) :=
  lixChern_eq_of_rank n _ hcont hproj (lixRank n dd) (one_le_lixRank n dd)
    (fun x => rank_lixBundle n G hGc hGu x) k

/-! ## 3. The classes in the ring -/

open Classical in
/-- The mod-2 Chern classes of a family, in `TotalH`, totally defined. -/
def lixChernOf (n : ℕ) (chern : LixChernDeg n dd) (P : LixFamily n dd) (k : ℕ) :
    TotalH (lixN n dd) :=
  if h : Continuous P ∧ (∀ p, IsStarProjection (P p))
  then TotalH.of (lixN n dd) (2 * k) (chern P h.1 h.2 k)
  else 0

/-- **The branch is always taken on a mapping torus.** -/
theorem lixChernOf_mappingTorus (n : ℕ) (chern : LixChernDeg n dd)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (k : ℕ) :
    lixChernOf n chern (mappingTorus (Gen.Vmat n) G circHoriz circHeight) k
      = TotalH.of (lixN n dd) (2 * k)
        (chern (mappingTorus (Gen.Vmat n) G circHoriz circHeight)
          (continuous_mappingTorus_lix n hGc) (isStarProjection_mappingTorus_lix n hGu) k) := by
  rw [lixChernOf,
    dif_pos (And.intro (continuous_mappingTorus_lix n hGc)
      (isStarProjection_mappingTorus_lix n hGu))]

end

/-! Audited on every build. -/

#audit_axioms KGen.lixChern_mappingTorus
#audit_axioms KGen.lixChernOf_mappingTorus

end KGen
end CharClass
end GroupApproximation
