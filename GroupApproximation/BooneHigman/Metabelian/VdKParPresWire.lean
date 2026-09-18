import GroupApproximation.BooneHigman.Metabelian.VdKParPresKernel
import GroupApproximation.BooneHigman.Metabelian.VdKInjDirectWire
import GroupApproximation.BooneHigman.Metabelian.VdKInjDirectTrans
import GroupApproximation.Meta.AxiomGuard

/-!
# The parabolic presentation, part 3: the residual and its strength

Lane `bh-met-92g`.  Target: `vdkInjCocycle_ParRetractAt (r + 3) R` for `sr(R) ≤ r`, built from
an explicit presentation of the parabolic `P = vdkRowParSubgroup`.

## What is proved (unconditionally, every `R`, every `n`)

* Generation (`vdkParPres_closure`): `P = ⟨stab(St_n(R)), x_{i,last}(a)⟩`.
* The presentation map `Π : R^n ⋊ St_n(R) ↠ P` (`vdkParPres_Pi`, `vdkParPres_range`).
  Its source is presented by the relations of `St_n(R)`, the additivity and commutation of the
  `x_{i,last}`, and `stab g · x(v) · stab g⁻¹ = x(M_g v)`.
* `φ` on the generators (`vdkParPres_retract`): `stab g ↦ g` and `x_{i,last}(a) ↦ 1`.  The
  relations of the presentation are respected because `φ` is `rightHom`
  (`vdkParPres_retract_stab`, `vdkParPres_retract_col`).
* **The hidden relations** (`vdkParPres_ker_eq`): `ker Π = inr (ker stab_n) ≤ inr K₂(n, R)`.

## Residual: `vdkParPres_NoHiddenRelStatement`

For `sr(R) ≤ r`, `ker Π = ⊥` at `n = r + 3`.  That is: `P` has the presentation
`R^n ⋊ St_n(R)`, with no hidden relations in the parabolic.

**LOUD (strength): EQUIVALENT, not strictly weaker.**  For every ring and every `n`,
`NoHiddenRel n R ↔ Injective (stab n R) ↔ Injective (K2Stab n R) ↔ ParRetractAt n R`
(`vdkParPres_noHiddenRel_iff_K2Stab_injective`, `vdkParPres_parRetract_iff_noHiddenRel`).
The obstruction to descending `rightHom` along `Π` is exactly `ker Π = inr (ker stab_n)`.
So the residual is
* `vdkInjDirect_TransitiveInjStatement` (`vdkParPres_statement_iff_transitiveInj`), and
* `vdkStab_InjStabStatement` (`vdkParPres_statement_iff_injStab`), which is van der Kallen's
  injective stability for `K₂`.

It is smaller only in **proof content**.  Generation, the presentation map, the explicit `φ`
and all relator checks are done here.  The St-level "no hidden relations", i.e. the vdK
injectivity theorem, is **not** proved.  It is not used as a hypothesis anywhere.

**Truth.**  It is true by van der Kallen's theorem, which is not used here.  The matrix-level
shadow is checked in `$SP/bh-met-92g/check.py` over `ZMod 4`, `ZMod 6`, `F₂[s]/(s²)` and `ZMod 2`
(n = 3).  It checks the semidirect law of `(v, A) ↦ [[A, v], [0, 1]]`, its injectivity, the
generation of the image, and that the upper-left block is a homomorphism satisfying the
generator values of `φ` and respecting every relation among the generators.  No failure.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Residual** (lane `bh-met-92g`): no hidden relations in the parabolic in the stable
range.  LOUD: equivalent to `vdkStab_InjStabStatement`, not strictly weaker. -/
def vdkParPres_NoHiddenRelStatement : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), vdkStab_StableRangeLE R r →
    vdkParPres_NoHiddenRel (r + 3) R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_NoHiddenRelStatement

/-- **Endpoint**: the residual gives the target, with the explicit retraction
`vdkParPres_retract`. -/
theorem vdkParPres_parRetract_of_statement (h : vdkParPres_NoHiddenRelStatement)
    (R : Type) [CommRing R] (r : ℕ) (hsr : vdkStab_StableRangeLE R r) :
    vdkInjCocycle_ParRetractAt (r + 3) R :=
  vdkParPres_parRetract_of_noHiddenRel (h R r hsr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_parRetract_of_statement

/-- The target gives the residual back: the target is equivalent to the residual. -/
theorem vdkParPres_statement_of_parRetract
    (h : ∀ (R : Type) [CommRing R] (r : ℕ), vdkStab_StableRangeLE R r →
      vdkInjCocycle_ParRetractAt (r + 3) R) :
    vdkParPres_NoHiddenRelStatement := by
  intro R _ r hsr
  exact vdkParPres_noHiddenRel_of_parRetract (h R r hsr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_statement_of_parRetract

/-- **LOUD (strength)**: the residual is equivalent to `vdkInjDirect_TransitiveInjStatement`. -/
theorem vdkParPres_statement_iff_transitiveInj :
    vdkParPres_NoHiddenRelStatement ↔ vdkInjDirect_TransitiveInjStatement := by
  constructor
  · intro h R _ r hsr _
    exact vdkParPres_noHiddenRel_iff_K2Stab_injective.mp (h R r hsr)
  · intro h R _ r hsr
    exact vdkParPres_noHiddenRel_iff_K2Stab_injective.mpr
      (h R r hsr (vdkInjDirect_rowTransitive_of_stableRange hsr))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_statement_iff_transitiveInj

/-- **LOUD (strength)**: the residual is equivalent to `vdkStab_InjStabStatement`, i.e. to
van der Kallen's injective stability for `K₂`. -/
theorem vdkParPres_statement_iff_injStab :
    vdkParPres_NoHiddenRelStatement ↔ vdkStab_InjStabStatement := by
  constructor
  · intro h
    exact vdkInjDirect_injStab_of_transitive (vdkParPres_statement_iff_transitiveInj.mp h)
  · intro h R _ r hsr
    exact vdkParPres_noHiddenRel_iff_K2Stab_injective.mpr (h R r (r + 3) hsr le_rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkParPres_statement_iff_injStab

end GroupApproximation.BooneHigman.Metabelian.ElemFP
