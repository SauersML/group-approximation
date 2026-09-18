import GroupApproximation.BooneHigman.Metabelian.VdKInjCocycleRetract
import GroupApproximation.BooneHigman.Metabelian.VdKInjDiag
import GroupApproximation.Meta.AxiomGuard

/-!
# Row cocycles and retractions, part 3: the residual for the polynomial family

Lane `bh-met-91y`.  Target: `vdkInjAct_CocycleStatement`, at least for
`R_k = MvPolynomial (Fin k) (ZMod p)`, the family of `vdkInj_DiagStatement`.

## What is proved (unconditionally)

* `vdkInjCocycle_retractStatement_iff`: `vdkInjAct_CocycleStatement` is equivalent to
  `vdkInjCocycle_RetractStatement`.  The latter asks for a retraction
  `φ : rowStab(e_last) →* St_{r+3}(R)` of `stab`.  Both directions are explicit constructions
  (`VdKInjCocycleRetract.lean`) and use no Step A.
* `vdkInjCocycle_diag_of_polyRetract`: the polynomial-family residual gives
  `vdkInj_DiagStatement`, through the base-point argument of `VdKInjActInj.lean`.
* `vdkInjCocycle_polyRetract_of_cocycle`: the target gives the residual.

## Residual: `vdkInjCocycle_PolyRetractStatement`

For `p` prime, `k > 0` and `sr(R_k) ≤ r`, some `φ : rowStab(e_last) →* St_{r+3}(R_k)` satisfies
`φ (stab g) = g` for all `g`.

**LOUD (strength): not strictly weaker.**
* It is **equivalent** to `vdkInjAct_CocycleStatement` restricted to the polynomial family
  (the per-ring equivalence `vdkInjCocycle_cocycle_iff_retract`).
* Under Step A (`vdkInjCoset_RowStabStatement`) it is **equivalent** to injectivity of
  `K2Stab (r + 3) R_k` for the family (`vdkInjCocycle_polyRetract_iff_injective_of_rowStab`).
  By `vdkRowCoreX_diag_iff_injective`, that is `vdkInj_DiagStatement` itself.
* Without Step A it is a priori **stronger** than injectivity.  A retraction on the parabolic
  image `P` alone is exactly injectivity (`vdkInjCocycle_parRetract_iff_injective`).  The
  residual needs `φ` on all of `rowStab(e_last) ⊇ P`.

It is smaller only in **proof content**: the action, the relator checks and both translations
(cocycle ↔ retraction) are done here.  The explicit van der Kallen cocycle from stable-range
data is **not** constructed.

**Truth.**  It holds whenever Step A and `K2Stab` injectivity hold for the family (the truth
theorem below).  Neither is proved here.  A Python check on `E_3` over `ZMod 4`, `ZMod 6` and
`F_2[s]/(s²)` finds no failure of the retraction ⟹ cocycle construction.  There the retraction
is the upper-left block, and every `add` / `commute` / `adjacent` identity and basedness hold.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- The target in retraction form: for `sr(R) ≤ r`, a retraction of `stab` on
`rowStab(e_last) ≤ St_{r+4}(R)`. -/
def vdkInjCocycle_RetractStatement : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), vdkStab_StableRangeLE R r →
    vdkInjDirect_RowTransitive R r → vdkInjCocycle_RetractAt (r + 3) R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_RetractStatement

/-- **Unconditional equivalence** with the target, with no Step A. -/
theorem vdkInjCocycle_retractStatement_iff :
    vdkInjCocycle_RetractStatement ↔ vdkInjAct_CocycleStatement := by
  constructor
  · intro h R _ r hsr htr
    exact vdkInjCocycle_cocycle_of_retract (h R r hsr htr)
  · intro h R _ r hsr htr
    obtain ⟨c, hc, hb⟩ := h R r hsr htr
    exact vdkInjCocycle_retract_of_cocycle hc hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_retractStatement_iff

/-- **Residual** (lane `bh-met-91y`): a retraction of `stab` on `rowStab(e_last)` for the
polynomial family.  LOUD: equivalent to the polynomial-family target, not strictly weaker. -/
def vdkInjCocycle_PolyRetractStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k r : ℕ, 0 < k →
    vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) r →
      vdkInjCocycle_RetractAt (r + 3) (MvPolynomial (Fin k) (ZMod p))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_PolyRetractStatement

/-- **Endpoint**: the residual gives `vdkInj_DiagStatement`. -/
theorem vdkInjCocycle_diag_of_polyRetract (h : vdkInjCocycle_PolyRetractStatement) :
    vdkInj_DiagStatement := by
  intro p hp k r hk hsr u _ hu
  exact vdkInjCocycle_injective_of_retract (h p hp k r hk hsr)
    (hu.trans (map_one (K2Stab (r + 3) (MvPolynomial (Fin k) (ZMod p)))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_diag_of_polyRetract

/-- The target gives the residual: specialise to the polynomial family. -/
theorem vdkInjCocycle_polyRetract_of_cocycle (h : vdkInjAct_CocycleStatement) :
    vdkInjCocycle_PolyRetractStatement := by
  intro p hp k r hk hsr
  obtain ⟨c, hc, hb⟩ := h (MvPolynomial (Fin k) (ZMod p)) r hsr
    (vdkInjDirect_rowTransitive_of_stableRange hsr)
  exact vdkInjCocycle_retract_of_cocycle hc hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_polyRetract_of_cocycle

/-- **Strength (LOUD).**  Under Step A the residual is equivalent to `K2Stab` injectivity for
the family.  By `vdkRowCoreX_diag_iff_injective`, that is `vdkInj_DiagStatement`.  The `⟸`
direction is also the truth check of the residual. -/
theorem vdkInjCocycle_polyRetract_iff_injective_of_rowStab
    (hA : vdkInjCoset_RowStabStatement) :
    vdkInjCocycle_PolyRetractStatement ↔
      ∀ p : ℕ, p.Prime → ∀ k r : ℕ, 0 < k →
        vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) r →
          Function.Injective (K2Stab (r + 3) (MvPolynomial (Fin k) (ZMod p))) := by
  constructor
  · intro h p hp k r hk hsr
    exact vdkInjCocycle_injective_of_retract (h p hp k r hk hsr)
  · intro h p hp k r hk hsr
    exact (vdkInjCocycle_retract_iff_injective_of_rowStab
      (hA (MvPolynomial (Fin k) (ZMod p)) r (r + 3) hsr le_rfl)).mpr (h p hp k r hk hsr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_polyRetract_iff_injective_of_rowStab

end GroupApproximation.BooneHigman.Metabelian.ElemFP
