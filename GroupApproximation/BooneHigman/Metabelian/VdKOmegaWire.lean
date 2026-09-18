import GroupApproximation.BooneHigman.Metabelian.VdKOmegaAmalgam
import GroupApproximation.BooneHigman.Metabelian.VdKParPresWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The amalgam route, part 4: wiring into `vdkParPres_NoHiddenRelStatement`

Lane `bh-met-92j`.

* `vdkOmega_HasOmega n R`: there exist a set `Ω`, actions `α` of the parabolic `P̃` and `β` of
  the opposite parabolic `P̃⁻` on `Ω`, and a point `ω₀`, such that
  * `α` and `β` agree on `St_n(R)`;
  * the mixed relation `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` holds on `Ω`;
  * `St_n(R)` acts freely at `ω₀`.
* `vdkOmega_hasOmega_iff_noHiddenRel`: **`vdkOmega_HasOmega n R ↔ vdkParPres_NoHiddenRel n R`**.
  * `→` is the amalgam `LastRootAction` (`VdKOmegaAmalgam`).  All Steinberg relations of
    `St_{n+1}(R)` except the mixed one come for free from the two semidirect products.
  * `←` is the regular action `Ω = St_{n+1}(R)`, `ω₀ = 1`.
* `vdkOmega_Statement`: `vdkOmega_HasOmega (r + 3) R` whenever `sr(R) ≤ r`.
* `vdkOmega_noHiddenRelStatement_of_statement`: it implies `vdkParPres_NoHiddenRelStatement`.

**LOUD: the residual is only logically equivalent, not strictly weaker.**
`vdkOmega_statement_iff` proves `vdkOmega_Statement ↔ vdkParPres_NoHiddenRelStatement`.  What is
removed is proof content: to prove the target one now only has to build `Ω` with two parabolic
actions (van der Kallen's `Ω`, made of unimodular-row data) and check agreement, the single mixed
family and freeness.  Every other Steinberg relation is discharged here, unconditionally.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- Glued parabolic actions, with `St_n(R)` acting freely at a point. -/
def vdkOmega_HasOmega (n : ℕ) (R : Type) [CommRing R] : Prop :=
  ∃ (Ω : Type) (α : vdkParPres_Tilde n R →* Equiv.Perm Ω)
    (β : vdkOmega_TildeMinus n R →* Equiv.Perm Ω) (ω₀ : Ω),
    vdkOmega_Agree α β ∧ vdkOmega_Mixed α β ∧
      ∀ g : St n R, α (vdkParPres_inr g) ω₀ = ω₀ → g = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_HasOmega

variable {n : ℕ} {R : Type} [CommRing R]

theorem vdkOmega_stab_injective_of_hasOmega (h : vdkOmega_HasOmega n R) :
    Function.Injective (stab n R) := by
  obtain ⟨Ω, α, β, ω₀, hαβ, hmix, hfree⟩ := h
  exact vdkOmega_stab_injective_of_omega α β hαβ hmix ω₀ hfree

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_stab_injective_of_hasOmega

/-- The truth direction: the regular action of `St_{n+1}(R)` on itself, pulled back along `Π`
and `Π⁻`. -/
theorem vdkOmega_hasOmega_of_stab_injective (hinj : Function.Injective (stab n R)) :
    vdkOmega_HasOmega n R := by
  let T := MulAction.toPermHom (St (n + 1) R) (St (n + 1) R)
  refine ⟨St (n + 1) R, T.comp vdkParPres_Pi, T.comp vdkOmega_PiMinus, 1, ?_, ?_, ?_⟩
  · intro g
    change T (vdkParPres_Pi (vdkParPres_inr g)) = T (vdkOmega_PiMinus (vdkOmega_inrMinus g))
    rw [vdkParPres_Pi_inr, vdkOmega_PiMinus_inr]
  · intro i k h a b
    change ⁅T (vdkParPres_Pi (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i a)))),
      T (vdkOmega_PiMinus (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single k b))))⁆ =
      T (vdkParPres_Pi (vdkParPres_inr (x i k h (a * b))))
    rw [← map_commutatorElement, vdkOmega_Pi_inl_single, vdkOmega_PiMinus_inl_single,
      vdkParPres_Pi_inr, stab_x]
    exact congrArg T (x_commutator i.castSucc (Fin.last n) k.castSucc (Fin.castSucc_ne_last i)
      (Fin.castSucc_ne_last k).symm (fun e ↦ h (Fin.castSucc_inj.mp e)) a b)
  · intro g hg
    have h2 : vdkParPres_Pi (vdkParPres_inr g) * 1 = 1 := hg
    rw [mul_one, vdkParPres_Pi_inr] at h2
    exact hinj (h2.trans (map_one (stab n R)).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_hasOmega_of_stab_injective

theorem vdkOmega_hasOmega_iff_noHiddenRel :
    vdkOmega_HasOmega n R ↔ vdkParPres_NoHiddenRel n R := by
  rw [vdkParPres_noHiddenRel_iff_stab_injective]
  exact ⟨vdkOmega_stab_injective_of_hasOmega, vdkOmega_hasOmega_of_stab_injective⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_hasOmega_iff_noHiddenRel

/-- **The residual** (logically equivalent to `vdkParPres_NoHiddenRelStatement`, see
`vdkOmega_statement_iff`): glued parabolic actions exist in the stable range. -/
def vdkOmega_Statement : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), vdkStab_StableRangeLE R r → vdkOmega_HasOmega (r + 3) R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_Statement

/-- **Endpoint.**  The residual implies the target. -/
theorem vdkOmega_noHiddenRelStatement_of_statement (h : vdkOmega_Statement) :
    vdkParPres_NoHiddenRelStatement := by
  intro R _ r hr
  exact vdkOmega_hasOmega_iff_noHiddenRel.mp (h R r hr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_noHiddenRelStatement_of_statement

theorem vdkOmega_statement_of_noHiddenRelStatement (h : vdkParPres_NoHiddenRelStatement) :
    vdkOmega_Statement := by
  intro R _ r hr
  exact vdkOmega_hasOmega_iff_noHiddenRel.mpr (h R r hr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_statement_of_noHiddenRelStatement

/-- **LOUD: equivalence.**  The residual is equivalent to the target, not strictly weaker. -/
theorem vdkOmega_statement_iff : vdkOmega_Statement ↔ vdkParPres_NoHiddenRelStatement :=
  ⟨vdkOmega_noHiddenRelStatement_of_statement, vdkOmega_statement_of_noHiddenRelStatement⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_statement_iff

end GroupApproximation.BooneHigman.Metabelian.ElemFP
