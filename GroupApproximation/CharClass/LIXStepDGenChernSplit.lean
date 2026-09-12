import GroupApproximation.CharClass.LIXStepDGenData
import GroupApproximation.CharClass.ParityEvenTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# `WuStepDData` from a Künneth decomposition and a slice

Lane `lx-slice2` of the LIX strongest swarm: residual (b) of
`Gen.lemmaTwoFor_powers_two_lixChernOf` (`CharClass/LIXLemmaTwoGenTwo.lean`), the binder
`data`.

`Gen.WuStepDData` asks for three coefficient families and five facts about them: `tx_inj`,
`gamma_eq`, `sq_b`, `split` and `slice`.  This file assembles the record over an abstract
base from a decomposition of the classes, the splitting principle, and the value of the
classes on a slice.  The real objects enter only through those hypotheses.

## The slice needs no pinned splitting

At rank two the splitting was pinned (`LemmaTwoStepDPinned.lean`) because `hslice` was stated
against a chosen `ChernSplit`.  Here the coefficient `a k` of *any* decomposition
`γ k = p^* (a k) + t · x · p^* (b k)` is `s^* (γ k)` for a section `s` of `p` on which the
degree-one class `t` dies: `s^*` undoes `p^*` on the first term and kills the second.  So
`slice` reduces to the value of the classes restricted along the slice, whatever
decomposition was chosen, and the record takes the decomposition as an existential.

## Main declarations

* `Gen.eq_map_section_of_split` — `a k = s^* (γ k)`, for every decomposition.
* `Gen.map_tClass_eq_zero_of_const` — `t` dies along a map that is constant on the circle.
* `Gen.WuStepDData.ofSection` — the record.
-/

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory

set_option linter.unusedSectionVars false

namespace Gen

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {N Y S₁ Sodd : TopCat.{0}}

/-- **The pullback coefficient of a decomposition is the restriction along a slice.**  No
property of the decomposition is used beyond its defining equation, so this holds for every
choice of `a` and `b` at once. -/
theorem eq_map_section_of_split {n : ℕ} {p : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
    {σ₁ : Hmod2 S₁ 1} {σodd : Hmod2 Sodd (2 * n + 1)} {γ : ℕ → TotalH N}
    {a b : ℕ → TotalH Y}
    (hγ : ∀ k : ℕ, γ k = TotalH.map p (a k)
      + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p (b k))
    (s : Y ⟶ N) (hsp : s ≫ p = 𝟙 Y) (hst : TotalH.map s (Wu.tClass q₁ σ₁) = 0) (k : ℕ) :
    a k = TotalH.map s (γ k) := by
  rw [hγ k, map_add, map_mul, map_mul, hst, zero_mul, zero_mul, add_zero,
    ← Wu.totalH_map_comp, hsp, Wu.totalH_map_id]

/-- **The degree-one class dies along a map that is constant on the circle**: it is pulled
back from the circle, and a constant map kills every positive degree. -/
theorem map_tClass_eq_zero_of_const {Y' Z : Type} [TopologicalSpace Y'] [TopologicalSpace Z]
    {q₁ : N ⟶ TopCat.of Z} (σ₁ : Hmod2 (TopCat.of Z) 1) (s : TopCat.of Y' ⟶ N) (c : Z)
    (hs : s ≫ q₁ = cmap (ContinuousMap.const Y' c)) :
    TotalH.map s (Wu.tClass q₁ σ₁) = 0 := by
  rw [Wu.tClass, ← Wu.totalH_map_comp, hs, TotalH.map_of,
    pull_const_eq_zero Y' c 1 (by omega) σ₁, map_zero]

/-- **`Gen.WuStepDData` from a decomposition, the splitting principle and the slice value.**

* `hdec` — the Künneth decomposition with instability of the `z`-coefficient, existentially
  (owner `lx-kunneth`, `KnLix.gamma_split_of_graded`);
* `htx` — Künneth uniqueness (`KnLix.tx_inj`);
* `hsplit` — the splitting principle (`Gen.hasSplitting_lixN`);
* `s`, `hsp`, `hst` — a section of `p` on which `t` dies;
* `hval` — the classes restricted along `s` are the slice polynomial's coefficients.

The coefficient families are read off `hdec` by choice; `eq_map_section_of_split` is why the
choice does not matter for `slice`. -/
def WuStepDData.ofSection (n : ℕ) (dd : Fin ℓ → ℕ) {p : N ⟶ Y} {q₁ : N ⟶ S₁}
    {qodd : N ⟶ Sodd} {σ₁ : Hmod2 S₁ 1} {σodd : Hmod2 Sodd (2 * n + 1)} {γ : ℕ → TotalH N}
    (hdec : ∃ a b : ℕ → TotalH Y,
      (∀ k : ℕ, γ k = TotalH.map p (a k)
        + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p (b k)) ∧
      (∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH Y j (b k) = 0))
    (htx : ∀ u v : TotalH Y,
      TotalH.map p u + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p v = 0 → v = 0)
    (hsplit : Wu.HasSplitting N γ)
    (s : Y ⟶ N) (hsp : s ≫ p = 𝟙 Y) (hst : TotalH.map s (Wu.tClass q₁ σ₁) = 0)
    (gen : Fin ℓ → TotalH Y)
    (hval : ∀ q : ℕ, TotalH.map s (γ q) = (sliceClass Finset.univ gen dd).coeff q) :
    WuStepDData n dd p q₁ qodd σ₁ σodd γ where
  a := hdec.choose
  b := hdec.choose_spec.choose
  gen := gen
  tx_inj := htx
  gamma_eq := hdec.choose_spec.choose_spec.1
  sq_b := hdec.choose_spec.choose_spec.2
  split := hsplit
  slice := fun q =>
    (eq_map_section_of_split hdec.choose_spec.choose_spec.1 s hsp hst q).trans (hval q)

end Gen

/-! Audited on every build. -/

#audit_axioms Gen.eq_map_section_of_split
#audit_axioms Gen.map_tClass_eq_zero_of_const
#audit_axioms Gen.WuStepDData.ofSection

end CharClass
end GroupApproximation

end
