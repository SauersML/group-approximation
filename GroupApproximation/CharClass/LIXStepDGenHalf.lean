import GroupApproximation.CharClass.LIXStepDGenData
import GroupApproximation.CharClass.LIXStepDGenModP

/-!
# The Step D half of Lemma 2 at rank `n`, for every section and every prime dividing the rank

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4 and §1.6).

`Manuscript/NinetyNineProblems/ProblemLIXStrong.lean`'s `LemmaTwoHoldsForSections n b` asks
for `LIX.Gen.LemmaTwoFor n (lixDD n j) (b j)` at every stage `j`, and the rank-two glue
(`CharClass/LemmaTwoGlue.lean`, `CharClass/LemmaTwoStepA.lean`) proves such a statement from
two cohomological halves about one class `topClass` of the mapping torus:

* **Step C**, which depends on the section: `topClass W_G ≠ 0` for the corner unitaries `G`
  carrying the constant section to `b`;
* **Step D**, which does not: `topClass W_G = 0` for **every** corner unitary `G`.

This file names the second half at rank `n` (`Gen.StepDHalf`) and proves it, at the top
Chern class, from the even side:

* at `p = 2` with `Even n`, from `sp-evenside-n`'s landed `Gen.stepD_of_wu`;
* at any prime `p ∣ n`, from `Gen.ModPStepDData.gamma_top_eq_zero`, which instantiates
  `sp-evenside`'s uniform `ParityPData`.

## Why one theorem serves every `k`

`Gen.StepDHalf n dd topClass` mentions neither the section nor the winding index: it
quantifies over every corner unitary of `V`.  So the Step D half of
`LemmaTwoHoldsForSections n (b k)` is the **same proposition for every `k`**, and the
theorems below discharge it once for the whole family `b k j m := joinPowNeg e₁ e₂ k (bVec n m)`.
The prime enters only through the coefficients of `topClass`, which is why the hypothesis
is `p ∣ n` and never a condition on `k`.

## Main results

* `Gen.StepDHalf` — the Step D half of Lemma 2 at rank `n`.
* `Gen.stepDHalf_of_wu`, `Gen.stepDHalf_of_wu_stage` — at `p = 2`.
* `Gen.stepDHalf_of_modP`, `Gen.stepDHalf_of_modP_stage` — at a prime `p ∣ n`, at every
  stage of the rank-`n` tower from the single hypothesis `p ∣ n`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59

namespace Gen

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {N Y S₁ Sodd : TopCat.{0}}

/-! ## 1. The Step D half at rank `n` -/

/-- **The Step D half of Lemma 2 at rank `n`**, for a class `topClass` of mapping tori with
values in `K`: the class vanishes on the mapping torus of **every** continuous corner
unitary of `V`.  It does not mention the section, so it is the same proposition for every
winding index. -/
def StepDHalf (n : ℕ) (dd : Fin ℓ → ℕ) {K : Type*} [Zero K]
    (topClass : (↥sphereOne × baseM n dd →
      Matrix (VIdx n dd ⊕ VIdx n dd) (VIdx n dd ⊕ VIdx n dd) ℂ) → K) : Prop :=
  ∀ G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ, Continuous G →
    (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
    topClass (mappingTorus (Vmat n) G circHoriz circHeight) = 0

/-! ## 2. At `p = 2` -/

/-- **The Step D half at rank `n`, mod 2**, at the top Chern class
`γ_{(∑ⱼ dⱼ) + n + 1}`.  This is `Gen.stepD_of_wu` in the vocabulary of the halves. -/
theorem stepDHalf_of_wu (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n)
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (hC : Wu.CartanTotal)
    (hS₁ : HasSphereCohomology S₁ 1) (hSodd : HasSphereCohomology Sodd (2 * n + 1))
    (σ₁ : Hmod2 S₁ 1) (σodd : Hmod2 Sodd (2 * n + 1))
    (γfun : (↥sphereOne × baseM n dd →
      Matrix (VIdx n dd ⊕ VIdx n dd) (VIdx n dd ⊕ VIdx n dd) ℂ) → ℕ → TotalH N)
    (hd : ∀ j, Even (dd j))
    (data : ∀ (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      WuStepDData n dd p q₁ qodd σ₁ σodd
        (γfun (mappingTorus (Vmat n) G circHoriz circHeight))) :
    StepDHalf n dd (fun W => γfun W ((∑ j, dd j) + (n + 1))) :=
  stepD_of_wu n hn hn2 p q₁ qodd hC hS₁ hSodd σ₁ σodd γfun hd data

/-- **The Step D half mod 2 at every stage of the rank-`n` tower**, from `Even n` alone. -/
theorem stepDHalf_of_wu_stage (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (j : ℕ)
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (hC : Wu.CartanTotal)
    (hS₁ : HasSphereCohomology S₁ 1) (hSodd : HasSphereCohomology Sodd (2 * n + 1))
    (σ₁ : Hmod2 S₁ 1) (σodd : Hmod2 Sodd (2 * n + 1))
    (γfun : (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) → ℕ → TotalH N)
    (data : ∀ (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      WuStepDData n (LIX.Gen.lixDD n j) p q₁ qodd σ₁ σodd
        (γfun (mappingTorus (Vmat n) G circHoriz circHeight))) :
    StepDHalf n (LIX.Gen.lixDD n j)
      (fun W => γfun W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1))) :=
  stepD_of_wu_stage n hn hn2 j p q₁ qodd hC hS₁ hSodd σ₁ σodd γfun data

/-! ## 3. At a prime dividing the rank -/

/-- **The Step D half at rank `n`, mod `p`**, at the top Chern class
`γ_{(∑ⱼ dⱼ) + n + 1}`, for every prime `p ∣ n` with `p ∣ dⱼ` for every `j`.  The data for
each corner unitary is `Gen.ModPStepDData`, and the conclusion is the instantiated
`ParityPData`. -/
theorem stepDHalf_of_modP (n p : ℕ) (hp : 2 ≤ p) (hn : 1 ≤ n) (hpn : p ∣ n)
    {R H : Type*} [CommRing R] [CommRing H] [ExpChar R p]
    (γfun : (↥sphereOne × baseM n dd →
      Matrix (VIdx n dd ⊕ VIdx n dd) (VIdx n dd ⊕ VIdx n dd) ℂ) → ℕ → H)
    (hd : ∀ j, p ∣ dd j)
    (data : ∀ (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      ModPStepDData n p dd R H (γfun (mappingTorus (Vmat n) G circHoriz circHeight))) :
    StepDHalf n dd (fun W => γfun W ((∑ j, dd j) + (n + 1))) :=
  fun G hc hu => (data G hc hu).gamma_top_eq_zero hp hn hpn hd

/-- **The Step D half mod `p` at every stage of the rank-`n` tower**, from `p ∣ n` alone:
the dimensions `lixDD n j i = 2^i · n` are all divisible by `p` (`LIX.Gen.dvd_lixDD`). -/
theorem stepDHalf_of_modP_stage (n p : ℕ) (hp : 2 ≤ p) (hn : 1 ≤ n) (hpn : p ∣ n) (j : ℕ)
    {R H : Type*} [CommRing R] [CommRing H] [ExpChar R p]
    (γfun : (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) → ℕ → H)
    (data : ∀ (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      ModPStepDData n p (LIX.Gen.lixDD n j) R H
        (γfun (mappingTorus (Vmat n) G circHoriz circHeight))) :
    StepDHalf n (LIX.Gen.lixDD n j)
      (fun W => γfun W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1))) :=
  stepDHalf_of_modP n p hp hn hpn γfun (LIX.Gen.dvd_lixDD hpn j) data

end Gen

#audit_axioms Gen.StepDHalf
#audit_axioms Gen.stepDHalf_of_wu
#audit_axioms Gen.stepDHalf_of_wu_stage
#audit_axioms Gen.stepDHalf_of_modP
#audit_axioms Gen.stepDHalf_of_modP_stage

end CharClass
end GroupApproximation

end
