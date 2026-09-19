import GroupApproximation.CharClass.LIXSectionManuscript

/-!
# The base as a left-nested chain of binary products

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`cc-thom`'s punctured-product recursion takes Künneth **one factor at a time**: fully
general Künneth needs Eilenberg–Zilber, which is in neither Mathlib nor the vendored tree.
So the base `N` has to be presented left-nested,

```text
(((S¹ × S⁵) × ℂP^{d₁}) × ℂP^{d₂}) × ⋯ ,
```

with each new factor adjoined on the **right**, so that every second factor is a sphere or
a `ℂP`.  The base this lane works with, `↥sphereOne × baseM dd`, has the dependent product
`∀ j : Fin ℓ, CP (dd j)` in its second slot, which has no Künneth factor.

This file supplies the missing translation, as the **binary step** rather than as a type
family: `baseSnocHomeo` peels one projective factor off to the right, and `baseNilHomeo`
is the base case.  Iterating the first from the second builds any left-nested chain, and
`cc-thom`'s `PuncturedAcyclic.congr'` then transports the conclusion back onto the
dependent product, which is the shape the C*-side's inductive limit actually uses.

## Main results

* `piFinSnocHomeo` — peel the **last** factor off a dependent finite product.  Mathlib and
  `cc-thom`'s `piFinSuccHomeo` both peel the *first*, which is the wrong end here.
* `baseSnocHomeo` — the binary step: the base for `ℓ + 1` is the base for `ℓ` times a
  single `ℂP`.
* `baseNilHomeo` — the base case: with no projective factors the base is `S¹ × S⁵`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. Peeling the last factor of a dependent product -/

/-- **Peel the last factor off a dependent finite product.**  `cc-thom`'s `piFinSuccHomeo`
peels the first factor, giving a right-nested chain; the punctured-product recursion needs
the other end. -/
def piFinSnocHomeo {n : ℕ} (X : Fin (n + 1) → Type) [∀ i, TopologicalSpace (X i)] :
    (∀ i, X i) ≃ₜ (∀ i : Fin n, X i.castSucc) × X (Fin.last n) where
  toFun f := (fun i => f i.castSucc, f (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv f := Fin.snoc_init_self f
  right_inv p := by simp
  continuous_toFun :=
    (continuous_pi fun i => continuous_apply i.castSucc).prodMk
      (continuous_apply (Fin.last n))
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact continuous_snd
    | cast j =>
      simp only [Fin.snoc_castSucc]
      exact (continuous_apply j).comp continuous_fst

/-! ## 2. The binary step for the LIX base -/

variable {ℓ : ℕ}

/-- **The binary step.**  The base with `ℓ + 1` projective factors is the base with `ℓ` of
them, times one `ℂP`, adjoined on the right.  Iterating this from `baseNilHomeo` produces
the left-nested chain `cc-thom`'s recursion consumes. -/
def baseSnocHomeo (dd : Fin (ℓ + 1) → ℕ) :
    (↥sphereOne × baseM dd)
      ≃ₜ (↥sphereOne × baseM (fun j => dd j.castSucc)) × CP (dd (Fin.last ℓ)) :=
  (((Homeomorph.refl (↥sphereOne)).prodCongr
        ((Homeomorph.refl (↥(unitVectors (Fin 3)))).prodCongr
          (piFinSnocHomeo (fun j : Fin (ℓ + 1) => CP (dd j))))).trans
    ((Homeomorph.refl (↥sphereOne)).prodCongr
      (Homeomorph.prodAssoc (↥(unitVectors (Fin 3)))
        (∀ j : Fin ℓ, CP (dd j.castSucc)) (CP (dd (Fin.last ℓ)))).symm)).trans
    (Homeomorph.prodAssoc (↥sphereOne)
      (↥(unitVectors (Fin 3)) × (∀ j : Fin ℓ, CP (dd j.castSucc)))
      (CP (dd (Fin.last ℓ)))).symm

/-- **The base case.**  With no projective factors the base is just `S¹ × S⁵`; the
dependent product over `Fin 0` is a one-point space. -/
def baseNilHomeo (dd : Fin 0 → ℕ) :
    (↥sphereOne × baseM dd) ≃ₜ ↥sphereOne × ↥(unitVectors (Fin 3)) :=
  (Homeomorph.refl (↥sphereOne)).prodCongr
    (Homeomorph.prodUnique (↥(unitVectors (Fin 3))) (∀ j : Fin 0, CP (dd j)))

end GroupApproximation.CharClass
