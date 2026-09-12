import GroupApproximation.CharClass.LIXSectionLocalHomeo
import GroupApproximation.CharClass.LIXSectionNesting
import GroupApproximation.CharClass.ThomToolkitInstance
import GroupApproximation.CharClass.ThomPuncturedPi

/-!
# Step E, first piece: the punctured-product vanishing at the LIX base

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C), taken from `cc-thom` as the piece
of their Step E written entirely in this lane's vocabulary.

`cc-thom`'s `EulerLocalAssembly.topChernClass_ne_zero_of_chain` takes as its first
hypothesis that the base `N` is **top-punctured acyclic**: `H^k(N ∖ z; F₂) = 0` in the top
degree.  Their recursion is binary and takes Künneth one factor at a time, so the
instantiation at

```text
N = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}
```

is an induction on the number of projective factors, peeling the **last** one each time.
That is exactly the shape `CharClass/LIXSectionNesting.lean` provides: `baseNilHomeo` for
the base case and `baseSnocHomeo` for the step, transported by
`PuncturedAcyclic.congr'`.

The degree bookkeeping closes on `Fin.sum_univ_castSucc`, matching the end that
`baseSnocHomeo` peels, and the total degree is `2 ∑ⱼ dⱼ + 6`, which is `lixTopDegree dd`.

## What is assumed, and by whom

* `hCPacyclic`, `kCP`, `kCPpunct` — the projective factor, owned by `cc-projective`.  The
  first follows from their green `punctureHomotopyEquiv` through `cc-thom`'s
  `puncturedAcyclic_of_homotopyEquiv`; the other two are their Künneth factor, not yet
  landed.
* `hbase` — the two sphere factors in **this lane's** models.  `cc-thom`'s green sphere
  case is stated for `Metric.sphere (0 : E) 1` in a real inner product space, while
  `sphereOne` and `unitVectors (Fin 3)` are different models, so the transport is a
  separate job; it is left as a hypothesis rather than guessed at.

All four are named hypotheses, never `sorry`, and the theorem becomes unconditional by
`exact` the moment they land.

## Main results

* `puncturedAcyclic_lixBase` — **the first hypothesis of `topChernClass_ne_zero_of_chain`**,
  at the LIX base.
* `puncturedAcyclic_lixBase_lixTopDegree` — the same, stated in the degree index this lane
  hands `cc-thom`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

section StepE

/-- **The punctured-product vanishing at the LIX base.**

Induction on the number of projective factors, peeling the last one with `baseSnocHomeo`
and transporting with `PuncturedAcyclic.congr'`.  The base case is `baseNilHomeo` against
the two sphere factors.  Nothing here needs a `CohomologyToolkit` argument: `cc-thom`
discharged it as a term. -/
theorem puncturedAcyclic_lixBase
    (hCPacyclic : ∀ d : ℕ, 0 < d → ∀ w : CP d, PuncturedAcyclic (CP d) (2 * d) w)
    (kCP : ∀ d : ℕ, 0 < d → KunnethFactor (CP d) (2 * d))
    (kCPpunct : ∀ d : ℕ, 0 < d → ∀ w : CP d,
      KunnethFactor ↥({w}ᶜ : Set (CP d)) (2 * d - 1))
    (hbase : ∀ w : ↥sphereOne × ↥(unitVectors (Fin 3)),
      PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w) :
    ∀ (ℓ : ℕ) (dd : Fin ℓ → ℕ), (∀ j, 0 < dd j) →
    ∀ z : ↥sphereOne × baseM dd,
      PuncturedAcyclic (↥sphereOne × baseM dd) (2 * (∑ j, dd j) + 6) z := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro dd _ z
    have hdeg : 2 * (∑ j : Fin 0, dd j) + 6 = 6 := by simp
    rw [hdeg]
    exact PuncturedAcyclic.congr' cohomologyToolkit (baseNilHomeo dd) rfl
      (hbase (baseNilHomeo dd z))
  | succ ℓ ih =>
    intro dd hdd z
    have hdeg : 2 * (∑ j : Fin (ℓ + 1), dd j) + 6
        = (2 * (∑ j : Fin ℓ, dd j.castSucc) + 6) + 2 * dd (Fin.last ℓ) := by
      rw [Fin.sum_univ_castSucc dd]
      ring
    rw [hdeg]
    refine PuncturedAcyclic.congr' cohomologyToolkit (baseSnocHomeo dd) rfl ?_
    have hprod := puncturedAcyclic_prod
      (x₀ := (baseSnocHomeo dd z).1) (y₀ := (baseSnocHomeo dd z).2)
      (kCP (dd (Fin.last ℓ)) (hdd (Fin.last ℓ)))
      (kCPpunct (dd (Fin.last ℓ)) (hdd (Fin.last ℓ)) (baseSnocHomeo dd z).2)
      (ih (fun j => dd j.castSucc) (fun j => hdd j.castSucc) (baseSnocHomeo dd z).1)
      (hCPacyclic (dd (Fin.last ℓ)) (hdd (Fin.last ℓ)) (baseSnocHomeo dd z).2)
    simpa using hprod

/-- The same, in the degree index this lane hands `cc-thom`. -/
theorem puncturedAcyclic_lixBase_lixTopDegree
    (hCPacyclic : ∀ d : ℕ, 0 < d → ∀ w : CP d, PuncturedAcyclic (CP d) (2 * d) w)
    (kCP : ∀ d : ℕ, 0 < d → KunnethFactor (CP d) (2 * d))
    (kCPpunct : ∀ d : ℕ, 0 < d → ∀ w : CP d,
      KunnethFactor ↥({w}ᶜ : Set (CP d)) (2 * d - 1))
    (hbase : ∀ w : ↥sphereOne × ↥(unitVectors (Fin 3)),
      PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin 3))) 6 w)
    {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (hdd : ∀ j, 0 < dd j) (z : ↥sphereOne × baseM dd) :
    PuncturedAcyclic (↥sphereOne × baseM dd) (lixTopDegree dd) z :=
  puncturedAcyclic_lixBase hCPacyclic kCP kCPpunct hbase ℓ dd hdd z

end StepE

end GroupApproximation.CharClass
