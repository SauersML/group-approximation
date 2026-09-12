import GroupApproximation.CharClass.LIXStepDGenParity
import GroupApproximation.CharClass.LIXShapeGeneric
import GroupApproximation.CharClass.LemmaTwoStepD
import GroupApproximation.Analysis.LIXLemmaTwoPropGeneric

/-!
# Step D at the real objects, generic in the rank

Lane `sp-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4).

`CharClass/LemmaTwoStepD.lean` wires the even side to the manuscript's objects at rank two:
`WuStepDData` bundles the remaining hypotheses for one bundle over the mapping torus base,
and `stepD_of_wu` is the Step D half of `LemmaTwoGlue.lean`'s `LemmaTwoInput`, concluding
`γ_{(∑ⱼ dⱼ)+3}(W_g) = 0` for every unitary Step A can produce.

This file does the same over `sp-tower`'s rank-generic shape layer
(`CharClass/LIXShapeGeneric.lean`): the base is `M = S^{2n+1} × Y`, the ambient is
`V = 𝟏^{n+1} ⊕ H` indexed by `Gen.VIdx n dd`, the Künneth generator of the odd sphere has
degree `2n + 1`, the `z`-component `b k` has degree `2k − (2n + 2)`, and the conclusion is
read at `r = (∑ⱼ dⱼ) + n + 1`.  The `F₂` mathematics is unchanged — it is uniform in the
rank, see the programme note §1.4 and `sp-design`'s report §3 — so this is a restatement
over the generic objects, and `§3` re-derives the landed rank-two declarations from it.

## Where the rank hides at rank two, and what it became

| rank two | rank `n` | where |
|---|---|---|
| `σ₅ : Hmod2 S₅ 5` | `σodd : Hmod2 Sodd (2 * n + 1)` | the odd sphere is `S^{2n+1}` |
| `2 * k < j + 6` | `2 * k < j + (2 * n + 2)` | `z = t x` has degree `2n + 2` |
| `(∑ⱼ dⱼ) + 3` | `(∑ⱼ dⱼ) + (n + 1)` | `V` has an `𝟏^{n+1}` block |
| `Wu.xClass q₅ σ₅` | `Gen.sphereClass qodd σodd` | the degree is pinned in the type |
| `baseM`, `VIdx`, `Vmat` | `Gen.baseM n`, `Gen.VIdx n`, `Gen.Vmat n` | `sp-tower`'s shape layer |

Two hypotheses of the rank-`n` statements have no rank-two counterpart: `Even n`, which is
the `p = 2` case of the programme's `p ∣ n` and is what makes `r = n + 1 + m` odd, and
`2 ≤ n`, which is the programme's standing assumption on the rank and is used only to feed
`ParityEven.lean`'s instability field (see `LIXStepDGenParity.lean` §4).  Both are
discharged by `le_rfl` and `even_two` at `n = 2`.

## The degree bridge is not restated

`ne_zero_of_degree_ne_zero` of `LemmaTwoStepD.lean` — Step C's nonvanishing in the single
graded piece `H^{2r}(N; F₂)`, read in the ring `TotalH N` — mentions neither the rank nor
the degree of anything, only `TotalH.of_eq_zero_iff`.  It is rank-generic as it stands and
is used unchanged; restating it here would be a duplicate.

## Main results

* `Gen.WuStepDData` — the even side's hypotheses for one bundle, at rank `n`.
* `Gen.WuStepDData.gamma_top_eq_zero` — `γ_{(∑ⱼ dⱼ)+n+1}(W) = 0`.
* `Gen.stepD_of_wu` — **the Step D half of `LemmaTwoInput`, at rank `n`**.
* `§3` — `Gen.ofRankTwo`, `Gen.toRankTwo` and `stepD_of_wu_of_gen`: the rank-two record is
  the `n = 2` record field by field, and the landed `stepD_of_wu` is the `n = 2` instance.
-/

noncomputable section

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

namespace Gen

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {N Y S₁ Sodd : TopCat.{0}}

/-! ## 1. `cc-wu`'s data at rank `n` -/

/-- **The hypotheses of the even side at rank `n`**, for one bundle over `N`.  The fields
are those of `CharClass.WuStepDData` with the degree of the odd sphere and the degree of
`z = t x` made into functions of the rank; `a_zero` and `a_odd` are again not fields, being
derived from `slice`, and the Cartan formula is again a hypothesis of the theorems rather
than a field, because it is quantified over the space and so depends on neither the corner
unitary nor the tower stage. -/
structure WuStepDData (n : ℕ) (dd : Fin ℓ → ℕ) (p : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (σ₁ : Hmod2 S₁ 1) (σodd : Hmod2 Sodd (2 * n + 1)) (γ : ℕ → TotalH N) where
  /-- The `H^*(Y)`-component of `γ k`, of degree `2k`. -/
  a : ℕ → TotalH Y
  /-- The `z H^*(Y)`-component of `γ k`, of degree `2k − (2n + 2)`; indexed by the
  **total** index, so `b k = 0` for `k < n + 1`. -/
  b : ℕ → TotalH Y
  /-- The degree-two generators `hⱼ = e(Lⱼ)`. -/
  gen : Fin ℓ → TotalH Y
  /-- Künneth uniqueness (owner `cc-cohom-api`, then `sp-coeff`); the rank-`n` form is
  `Gen.tx_inj_of_degreewise`. -/
  tx_inj : ∀ u v : TotalH Y,
    TotalH.map p u + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p v = 0 → v = 0
  /-- The Künneth decomposition of the Chern classes (owner `cc-cohom-api`). -/
  gamma_eq : ∀ k : ℕ,
    γ k = TotalH.map p (a k)
      + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p (b k)
  /-- Instability, in the only form used, at the rank-`n` degree of `b k`
  (`Gen.sq_b_of_grading`). -/
  sq_b : ∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH Y j (b k) = 0
  /-- The splitting principle (owner `cc-projective`), which subsumes the diagonal Wu
  relation.  Rank-free: the rank of `W` is existentially quantified inside it. -/
  split : Wu.HasSplitting N γ
  /-- The slice class of `W` is `∏ⱼ (1 + hⱼ)^{dⱼ}` (owner `cc-projective`).  Rank-free:
  the slice lives over `Y`.  This one hypothesis also supplies `a_zero` and `a_odd`. -/
  slice : ∀ q : ℕ, a q = (sliceClass Finset.univ gen dd).coeff q

/-- **The even side at rank `n`.**  `γ_{(∑ⱼ dⱼ)+n+1}(W) = 0` whenever every `dⱼ` is even
and the rank is even.  Only evenness is used, never the tower's powers of two. -/
theorem WuStepDData.gamma_top_eq_zero {n : ℕ} {p : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
    {σ₁ : Hmod2 S₁ 1} {σodd : Hmod2 Sodd (2 * n + 1)} {γ : ℕ → TotalH N}
    (D : WuStepDData n dd p q₁ qodd σ₁ σodd γ)
    (hn : Even n) (hn2 : 2 ≤ n) (hC : Wu.CartanTotal)
    (hS₁ : HasSphereCohomology S₁ 1) (hSodd : HasSphereCohomology Sodd (2 * n + 1))
    (hd : ∀ j, Even (dd j)) :
    γ ((∑ j, dd j) + (n + 1)) = 0 :=
  gamma_top_eq_zero_of_hasSplitting n hn hn2 p q₁ qodd hS₁ hSodd σ₁ σodd γ D.a D.b
    hC D.tx_inj D.gamma_eq D.sq_b D.split Finset.univ D.gen dd (fun j _ => hd j) D.slice

/-! ## 2. The Step D half of `LemmaTwoInput`, at rank `n` -/

/-- **Step D, at the real objects, at rank `n`.**  With `topClass W` the top mod-2 Chern
class `γ_{(∑ⱼ dⱼ)+n+1}(W)` in `TotalH N`, the even side gives exactly the `stepD`
hypothesis of the rank-`n` form of `LemmaTwoInput`: for *every* unitary Step A can produce
over `M = S^{2n+1} × Y`, the top class of the mapping torus vanishes. -/
theorem stepD_of_wu (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n)
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
    ∀ G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      γfun (mappingTorus (Vmat n) G circHoriz circHeight) ((∑ j, dd j) + (n + 1)) = 0 :=
  fun G hc hu => (data G hc hu).gamma_top_eq_zero hn hn2 hC hS₁ hSodd hd

/-! ## 2b. The same, at the dimensions the rank-`n` tower actually carries -/

/-- **Step D at every stage of the rank-`n` tower.**  Stage `j` carries the dimensions
`lixDD n j`, that is `d_i = n · 2^i` for `i < j`, and every one of them is even as soon as
the rank is (`LIX.Gen.even_lixDD`).  So the single hypothesis `Even n` discharges the
evenness at **every** stage at once, and the top index is `(∑ᵢ n·2^i) + n + 1`, the rank of
`V` at that stage.

This is the uniformity the limit needs: one theorem quantified over the stage `j`, not a
family of theorems proved stage by stage.  Nothing about the tower beyond `even_lixDD` is
used — `Gen.stepD_of_wu` itself is stated for an arbitrary coefficient datum `dd`. -/
theorem stepD_of_wu_stage (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (j : ℕ)
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
    ∀ G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      γfun (mappingTorus (Vmat n) G circHoriz circHeight)
        ((∑ i, LIX.Gen.lixDD n j i) + (n + 1)) = 0 :=
  stepD_of_wu n hn hn2 p q₁ qodd hC hS₁ hSodd σ₁ σodd γfun (LIX.Gen.even_lixDD hn j) data

/-! ## 3. The rank-two bridges

Every rank-two name of `LemmaTwoStepD.lean` is its own `Gen` declaration at `n = 2`.  The
record converts field by field with no proof obligation — at `n = 2` the odd sphere's
degree `2 * n + 1` **is** `5` and the bound `2 * n + 2` **is** `6` — and the landed
`stepD_of_wu` is the `n = 2` instance of `Gen.stepD_of_wu`, which is what
`stepD_of_wu_of_gen` checks in the kernel.

The rank-two record is written out in full (`_root_.GroupApproximation.CharClass.WuStepDData`)
rather than as `WuStepDData`: inside this namespace the short name is `Gen.WuStepDData`, and
a bridge that silently resolved to the wrong one of the two would prove nothing. -/

variable {S₅ : TopCat.{0}}

/-- The rank-two record **is** the rank-`n` record at `n = 2`. -/
def ofRankTwo {p : N ⟶ Y} {q₁ : N ⟶ S₁} {q₅ : N ⟶ S₅}
    {σ₁ : Hmod2 S₁ 1} {σ₅ : Hmod2 S₅ 5} {γ : ℕ → TotalH N}
    (D : _root_.GroupApproximation.CharClass.WuStepDData dd p q₁ q₅ σ₁ σ₅ γ) :
    WuStepDData 2 dd p q₁ q₅ σ₁ σ₅ γ :=
  ⟨D.a, D.b, D.gen, D.tx_inj, D.gamma_eq, D.sq_b, D.split, D.slice⟩

/-- ... and conversely. -/
def toRankTwo {p : N ⟶ Y} {q₁ : N ⟶ S₁} {q₅ : N ⟶ S₅}
    {σ₁ : Hmod2 S₁ 1} {σ₅ : Hmod2 S₅ 5} {γ : ℕ → TotalH N}
    (D : WuStepDData 2 dd p q₁ q₅ σ₁ σ₅ γ) :
    _root_.GroupApproximation.CharClass.WuStepDData dd p q₁ q₅ σ₁ σ₅ γ :=
  ⟨D.a, D.b, D.gen, D.tx_inj, D.gamma_eq, D.sq_b, D.split, D.slice⟩

@[simp] theorem ofRankTwo_a {p : N ⟶ Y} {q₁ : N ⟶ S₁} {q₅ : N ⟶ S₅}
    {σ₁ : Hmod2 S₁ 1} {σ₅ : Hmod2 S₅ 5} {γ : ℕ → TotalH N}
    (D : _root_.GroupApproximation.CharClass.WuStepDData dd p q₁ q₅ σ₁ σ₅ γ) :
    (ofRankTwo D).a = D.a := rfl

@[simp] theorem ofRankTwo_b {p : N ⟶ Y} {q₁ : N ⟶ S₁} {q₅ : N ⟶ S₅}
    {σ₁ : Hmod2 S₁ 1} {σ₅ : Hmod2 S₅ 5} {γ : ℕ → TotalH N}
    (D : _root_.GroupApproximation.CharClass.WuStepDData dd p q₁ q₅ σ₁ σ₅ γ) :
    (ofRankTwo D).b = D.b := rfl

end Gen

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {N Y S₁ S₅ : TopCat.{0}}

/-- **The landed `stepD_of_wu` is the `n = 2` instance of `Gen.stepD_of_wu`.**  The
statement is `LemmaTwoStepD.lean`'s verbatim: `baseM`, `VIdx` and `Vmat` are `sp-tower`'s
`Gen` names at `n = 2` definitionally, `5 = 2 * 2 + 1`, and the top index `3` is `2 + 1`.
Nothing consumes this declaration; it exists so that the subsumption is checked by the
kernel rather than asserted in a report. -/
theorem stepD_of_wu_of_gen (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
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
  Gen.stepD_of_wu 2 even_two le_rfl p q₁ q₅ hC hS₁ hS₅ σ₁ σ₅ γfun hd
    fun G hc hu => Gen.ofRankTwo (data G hc hu)

end CharClass
end GroupApproximation

end
