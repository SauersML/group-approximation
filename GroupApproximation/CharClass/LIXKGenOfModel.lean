import GroupApproximation.CharClass.LIXKGenBaseChart
import GroupApproximation.CharClass.RelativeLocalModelOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative group at each zero, identified with the local model, over a field

Lane `lix-powers` (odd-`p` twins of lane `lix-oddside-n`'s rank-`n` Step C).

`KGen.lixKRelModelIso n k dd i q` (`CharClass/LIXKGenBaseChart.lean`) identifies
`H^q(N, N ∖ z_i; F₂)` with `H^q(ℂ^r, ℂ^r ∖ 0; F₂)` by excision, the homeomorphism of punctured
pairs `KGen.lixKNbhdHomeo n k dd i`, and excision back.  The charts and the homeomorphism carry no
coefficients, so over any field `K` the same three steps give the same identification, with
lane `lix-coeff`'s `excisionIsoPointOf` and `relCohomologyCongrPointOf` in place of the `F₂` forms.

## Main declarations

* `KGen.lixKRelModelIsoOf K n k dd i q` — **the identification over `K`**.
* `KGen.lixKRelModelIsoOf_ne_zero` — a nonzero local class stays nonzero in the local model.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open Set CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-- **The relative group at the `i`-th zero, identified with the local model, over a field**, in
every degree. -/
def lixKRelModelIsoOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    relCohomology K (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q
      ≅ relCohomology K (TopCat.of (Fin (lixRank n dd) → ℂ))
        (puncturedSet (lixRank n dd)) q :=
  (excisionIsoPointOf K (lixN n dd) (lixKZero n k dd i) (lixKBC n k dd i).target
      (lixKBC n k dd i).open_target (lixKZero_mem_lixKBC_target n k dd i) q).trans
    ((relCohomologyCongrPointOf K (lixKNbhdHomeo n k dd i)
        (lixKZero_mem_lixKBC_target n k dd i) (zero_mem_lixKFC_target n k dd i)
        (lixKNbhdHomeo_zero n k dd i) q).trans
      (excisionIsoPointOf K (TopCat.of (Fin (lixRank n dd) → ℂ)) 0 (lixKFC n k dd i).target
        (lixKFC n k dd i).open_target (zero_mem_lixKFC_target n k dd i) q).symm)

/-- A nonzero class of the pair punctured at the `i`-th zero is nonzero in the local model. -/
theorem lixKRelModelIsoOf_ne_zero (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ)
    (i : Fin (k + 1)) (q : ℕ)
    {x : relCohomology K (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q} (hx : x ≠ 0) :
    (lixKRelModelIsoOf K n k dd i q).hom.hom x ≠ 0 :=
  ne_zero_of_isoOf (lixKRelModelIsoOf K n k dd i q) hx

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixKRelModelIsoOf_ne_zero

end GroupApproximation.CharClass
