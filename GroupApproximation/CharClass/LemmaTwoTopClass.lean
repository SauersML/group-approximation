import GroupApproximation.CharClass.LemmaTwoStepD
import GroupApproximation.CharClass.LIXStepEPunctured

/-!
# `topClass`: the one object both steps of Lemma 2 speak about

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3).

`CharClass/LemmaTwoGlue.lean`'s `LemmaTwoInput` existentially quantifies a `topClass` over
**all** matrix-valued families on `S¹ × M`, and asks for it to be nonzero on a mapping
torus (Step C) and zero on one (Step D).  Any two proofs that name different `topClass`es
never meet, so the definition has to be made once, here, and used by both sides.

## The shape, and why it is degreewise

`cc-thom`'s `topChernClass_ne_zero_of_chain` concludes `gamma ≠ 0` for a `gamma` in the
**single graded piece** `H^{2r}(N; F₂)`, while `cc-wu`'s even side speaks in the ring
`TotalH N`.  So the assignment is taken degreewise — `chern P _ _ k : Hmod2 N (2k)`, which
is exactly the shape of `cc-projective`'s `LerayHirschDegree.gamma` — and pushed into the
ring by `TotalH.of`.  `ne_zero_of_degree_ne_zero` then carries `cc-thom`'s nonvanishing
across, and `TotalH.of_eq_zero_iff` carries `cc-wu`'s vanishing back.

`lixChernOf` is **total**: `LemmaTwoInput` quantifies over every family, including ones
that are neither continuous nor projection-valued, so the definition branches on that
conjunction and is `0` off it.  On a mapping torus the branch is always taken, by
`mappingTorus_continuous` and `mappingTorus_isStarProjection`, and the two proof arguments
are irrelevant, so `lixChernOf_mappingTorus` is a `dif_pos` and nothing more.

## Main results

* `lixN`, `lixRank`, `LixChernDeg`, `lixChernOf`, `lixTopClass` — the definition.
* `lixChernOf_mappingTorus` — the identification on a mapping torus.
* `stepC_of_chain` — Step C for `lixTopClass`, from `cc-thom`'s conclusion.
* `stepD_of_topClass` — Step D for the same `lixTopClass`, from `cc-wu`'s data.
* `lemmaTwoInput_of` — **both steps, one `topClass`**: `LemmaTwoInput` assembled.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The definition -/

/-- The base `N = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}`, as an object of `TopCat`. -/
def lixN (dd : Fin ℓ → ℕ) : TopCat.{0} := TopCat.of (↥sphereOne × baseM dd)

/-- The rank `r = (∑ⱼ dⱼ) + 3` of the mapping torus, which `trace_Vmat` computes. -/
def lixRank (dd : Fin ℓ → ℕ) : ℕ := (∑ j, dd j) + 3

theorem lixTopDegree_eq_two_mul_lixRank (dd : Fin ℓ → ℕ) :
    lixTopDegree dd = 2 * lixRank dd := lixTopDegree_eq_two_mul_rank dd

/-- A family of matrices on `N`. -/
abbrev LixFamily (dd : Fin ℓ → ℕ) : Type :=
  ↥sphereOne × baseM dd → Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ

/-- **A degreewise mod-2 Chern class assignment** for projection-valued families on `N`,
in the shape `cc-projective`'s `LerayHirschDegree.gamma` has. -/
abbrev LixChernDeg (dd : Fin ℓ → ℕ) : Type :=
  ∀ P : LixFamily dd, Continuous P → (∀ p, IsStarProjection (P p)) →
    ∀ k : ℕ, Hmod2 (lixN dd) (2 * k)

open Classical in
/-- The mod-2 Chern classes of a family, in the ring, **totally** defined: `0` on families
that are not continuous projection-valued.  The branch condition is not decidable, so the
`dite` runs on `Classical.propDecidable`; that is invisible downstream, since every use
goes through `dif_pos`. -/
def lixChernOf (chern : LixChernDeg dd) (P : LixFamily dd) (k : ℕ) : TotalH (lixN dd) :=
  if h : Continuous P ∧ (∀ p, IsStarProjection (P p))
  then TotalH.of (lixN dd) (2 * k) (chern P h.1 h.2 k)
  else 0

/-- **`topClass`.**  The one object both steps of Lemma 2 speak about. -/
def lixTopClass (chern : LixChernDeg dd) (P : LixFamily dd) : TotalH (lixN dd) :=
  lixChernOf chern P (lixRank dd)

/-! ## 2. The identification on a mapping torus -/

variable {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

theorem continuous_mappingTorus_lix (hGc : Continuous G) :
    Continuous (mappingTorus Vmat G circHoriz circHeight) :=
  mappingTorus_continuous continuous_Vmat hGc isCircleChart_sphereOne

theorem isStarProjection_mappingTorus_lix (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (p : ↥sphereOne × baseM dd) :
    IsStarProjection (mappingTorus Vmat G circHoriz circHeight p) :=
  mappingTorus_isStarProjection hGu isCircleChart_sphereOne p

/-- **The branch is always taken on a mapping torus.**  Proof irrelevance does the rest:
the two arguments `chern` takes are `Prop`s, so which proofs are supplied does not
matter. -/
theorem lixChernOf_mappingTorus (chern : LixChernDeg dd) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (k : ℕ) :
    lixChernOf chern (mappingTorus Vmat G circHoriz circHeight) k
      = TotalH.of (lixN dd) (2 * k)
        (chern (mappingTorus Vmat G circHoriz circHeight)
          (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu) k) := by
  rw [lixChernOf,
    dif_pos (And.intro (continuous_mappingTorus_lix hGc)
      (isStarProjection_mappingTorus_lix hGu))]

/-! ## 3. Step C -/

/-- **Step C for `lixTopClass`.**  `cc-thom`'s `topChernClass_ne_zero_of_chain` concludes
nonvanishing in the single graded piece `H^{2r}(N; F₂)`; `ne_zero_of_degree_ne_zero`
carries that into the ring, which is where `lixTopClass` lives. -/
theorem stepC_of_chain (chern : LixChernDeg dd)
    (hchain : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      chern (mappingTorus Vmat G circHoriz circHeight)
        (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
        (lixRank dd) ≠ 0) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      lixTopClass chern (mappingTorus Vmat G circHoriz circHeight) ≠ 0 := by
  intro G hGc hGu hGe
  rw [lixTopClass, lixChernOf_mappingTorus chern hGc hGu]
  exact ne_zero_of_degree_ne_zero (hchain G hGc hGu hGe)

/-! ## 4. Step D, for the same `topClass` -/

variable {N Y S₁ S₅ : TopCat.{0}}

/-- **Step D for `lixTopClass`.**  One application of `stepD_of_wu` at `γfun` the same
`lixChernOf`, so the two steps provably speak about one object. -/
theorem stepD_of_topClass (chern : LixChernDeg dd)
    (p : lixN dd ⟶ Y) (q₁ : lixN dd ⟶ S₁) (q₅ : lixN dd ⟶ S₅) (hC : Wu.CartanTotal)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5) (hd : ∀ j, Even (dd j))
    (data : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      WuStepDData dd p q₁ q₅ σ₁ σ₅
        (lixChernOf chern (mappingTorus Vmat G circHoriz circHeight))) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      lixTopClass chern (mappingTorus Vmat G circHoriz circHeight) = 0 :=
  stepD_of_wu p q₁ q₅ hC hS₁ hS₅ σ₁ σ₅ (lixChernOf chern) hd data

/-! ## 5. Both steps, one `topClass` -/

/-- **`LemmaTwoInput`, assembled.**  Step C from `cc-thom`'s chain and Step D from
`cc-wu`'s data, about the *same* `lixTopClass`.  This is the last seam of Lemma 2: with it,
`lemmaTwoHolds_of` needs nothing that is not owned by a cohomology lane. -/
theorem lemmaTwoInput_of (chern : LixChernDeg dd)
    (p : lixN dd ⟶ Y) (q₁ : lixN dd ⟶ S₁) (q₅ : lixN dd ⟶ S₅) (hC : Wu.CartanTotal)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5) (hd : ∀ j, Even (dd j))
    (hchain : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ) (hGc : Continuous G)
      (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
      (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
      chern (mappingTorus Vmat G circHoriz circHeight)
        (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
        (lixRank dd) ≠ 0)
    (data : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      WuStepDData dd p q₁ q₅ σ₁ σ₅
        (lixChernOf chern (mappingTorus Vmat G circHoriz circHeight))) :
    LemmaTwoInput dd :=
  ⟨TotalH (lixN dd), inferInstance, lixTopClass chern, stepC_of_chain chern hchain,
    stepD_of_topClass chern p q₁ q₅ hC hS₁ hS₅ σ₁ σ₅ hd data⟩

end GroupApproximation.CharClass
