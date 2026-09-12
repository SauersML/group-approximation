import GroupApproximation.CharClass.LemmaTwoGlue
import GroupApproximation.CharClass.ParityInstance
import GroupApproximation.CharClass.SqDataInstance

/-!
# Step D at the real objects: the even side wired to `cc-wu`

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step D).

`cc-wu`'s `Wu.gamma_top_eq_zero_of_slice_totalH` is the even side at the real objects, and
it is green.  This file connects it to the `stepD` hypothesis of
`CharClass/LemmaTwoGlue.lean`'s `LemmaTwoInput`.

## Why this lives in its own module

`cs-endpoint` checked, and depends on, the fact that the import closure of
`CharClass/LemmaTwoStatement.lean` contains **no** cohomology module, so that
`Manuscript/NinetyNineProblems/ProblemLIX.lean` can be root-wired over
`LIX.LemmaTwoHolds` while the characteristic-class tower is still being built.  Wiring the
even side pulls in the whole cohomology layer, so it must not sit on that path.  Nothing
`LemmaTwoGlue` imports imports this file; it is a leaf, and it stays one until the tower is
complete.

## Two conveniences over calling `cc-wu` directly

* `WuStepDData` bundles the remaining hypotheses as one record, so that the even side can
  be quantified over the tower.  Three things are deliberately *not* in it.  `a_zero` and
  `a_odd` are derived by `cc-wu`'s endpoint from the slice.  The Wu relation is replaced by
  the splitting principle, `Wu.HasSplitting`, which subsumes it.  And the Cartan formula is
  a hypothesis of the *theorems* rather than a field, because `Wu.CartanTotal` is
  quantified over the space and so depends on neither the corner unitary nor the tower
  stage: carrying it inside a record that is itself quantified over every corner unitary
  would mean proving it once per unitary.
* `ne_zero_of_degree_ne_zero` is the bridge `cc-wu` points at: Step C produces
  nonvanishing in the single graded piece `H^{2r}(N; F₂)`, while the even side speaks in
  the ring `TotalH N`, and `TotalH.of_eq_zero_iff` identifies the two.

## Main results

* `WuStepDData`, `WuStepDData.gamma_top_eq_zero` — the even side, four hypotheses in the
  record plus the space-independent Cartan formula outside it.
* `stepD_of_wu` — **the Step D half of `LemmaTwoInput`**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The degree bridge -/

/-- **Step C's nonvanishing, read in the ring.**  A class concentrated in one degree is
nonzero in `TotalH` exactly when it is nonzero in its own degree. -/
theorem ne_zero_of_degree_ne_zero {X : TopCat.{0}} {n : ℕ} {c : Hmod2 X n} (h : c ≠ 0) :
    TotalH.of X n c ≠ 0 := fun hc => h ((TotalH.of_eq_zero_iff X n c).mp hc)

/-! ## 2. `cc-wu`'s data, with the slice doing three jobs -/

variable {N Y S₁ S₅ : TopCat.{0}}

/-- **The seven hypotheses of the even side**, for one bundle over `N`.  `a_zero` and
`a_odd` are not fields: `cc-wu`'s endpoint derives both from `slice`. -/
structure WuStepDData (dd : Fin ℓ → ℕ) (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5) (γ : ℕ → TotalH N) where
  /-- The `H^*(Y)`-component of `γ k`, of degree `2k`. -/
  a : ℕ → TotalH Y
  /-- The `t x H^*(Y)`-component of `γ k`, of degree `2k − 6`; indexed by the **total**
  index, so `b 0 = b 1 = b 2 = 0`. -/
  b : ℕ → TotalH Y
  /-- The degree-two generators `hⱼ = e(Lⱼ)`. -/
  gen : Fin ℓ → TotalH Y
  /-- Künneth uniqueness (owner `cc-cohom-api`). -/
  tx_inj : ∀ u v : TotalH Y,
    TotalH.map p u + Wu.tClass q₁ σ₁ * Wu.xClass q₅ σ₅ * TotalH.map p v = 0 → v = 0
  /-- The Künneth decomposition of the Chern classes (owner `cc-cohom-api`). -/
  gamma_eq : ∀ k : ℕ,
    γ k = TotalH.map p (a k) + Wu.tClass q₁ σ₁ * Wu.xClass q₅ σ₅ * TotalH.map p (b k)
  /-- Instability, in the only form used (owner `cc-cohom-api`). -/
  sq_b : ∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH Y j (b k) = 0
  /-- The splitting principle (owner `cc-projective`), which subsumes the diagonal Wu
  relation: `cc-wu` derives (Wu-diag) on the flag total space and pushes it down. -/
  split : Wu.HasSplitting N γ
  /-- The slice class of `W` is `∏ⱼ (1 + hⱼ)^{dⱼ}` (owner `cc-projective`).  This one
  hypothesis also supplies `a_zero` and `a_odd`. -/
  slice : ∀ q : ℕ, a q = (sliceClass Finset.univ gen dd).coeff q

variable {p : N ⟶ Y} {q₁ : N ⟶ S₁} {q₅ : N ⟶ S₅} {σ₁ : Hmod2 S₁ 1} {σ₅ : Hmod2 S₅ 5}
  {γ : ℕ → TotalH N}

/-- **The even side.**  `γ_{(∑ⱼ dⱼ)+3}(W) = 0` whenever every `dⱼ` is even.  Only evenness
is used, never the tower's powers of two. -/
theorem WuStepDData.gamma_top_eq_zero (D : WuStepDData dd p q₁ q₅ σ₁ σ₅ γ)
    (hC : Wu.CartanTotal)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (hd : ∀ j, Even (dd j)) :
    γ ((∑ j, dd j) + 3) = 0 :=
  Wu.gamma_top_eq_zero_of_hasSplitting p q₁ q₅ hS₁ hS₅ σ₁ σ₅ γ D.a D.b
    hC D.tx_inj D.gamma_eq D.sq_b D.split Finset.univ D.gen dd
    (fun j _ => hd j) D.slice

/-! ## 3. The Step D half of `LemmaTwoInput` -/

/-- **Step D, at the real objects.**  With `topClass W` the top mod-2 Chern class
`γ_{(∑ⱼ dⱼ)+3}(W)` in `TotalH N`, the even side gives exactly the `stepD` hypothesis of
`LemmaTwoInput`. -/
theorem stepD_of_wu (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
    (hC : Wu.CartanTotal)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5)
    (γfun : (↥sphereOne × baseM dd →
      Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ) → ℕ → TotalH N)
    (hd : ∀ j, Even (dd j))
    (data : ∀ (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      WuStepDData dd p q₁ q₅ σ₁ σ₅ (γfun (mappingTorus Vmat G circHoriz circHeight))) :
    ∀ G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat m) (G m)) →
      γfun (mappingTorus Vmat G circHoriz circHeight) ((∑ j, dd j) + 3) = 0 :=
  fun G hc hu => (data G hc hu).gamma_top_eq_zero hC hS₁ hS₅ hd

end GroupApproximation.CharClass
