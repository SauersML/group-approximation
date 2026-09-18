import GroupApproximation.BooneHigman.Metabelian.VdKOmegaBuildFull
import GroupApproximation.BooneHigman.Metabelian.VdKOmegaWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Building `Ω`, part 3: the residual `vdkOmegaBuild_Statement` and its wiring

Lane `bh-met-92v`.

**`Ω` IS NOT CONSTRUCTED HERE.**  The lane asked for an explicit `Ω` with `α`, `β`, `ω₀`
satisfying `vdkOmega_Agree`, `vdkOmega_Mixed` and freeness of `St_n(R)` at `ω₀`.  No honest
construction is available below the full theorem, for three reasons:

* Any such `Ω` already proves `Function.Injective (stab n R)`
  (`vdkOmega_stab_injective_of_hasOmega`).  So it *is* van der Kallen injective stability.
* The naive free `Ω = St_n(R) × R^n × R^n`, where columns translate the first vector and rows
  translate the second, satisfies `Agree` and freeness but **fails** `Mixed`: the two
  translations commute, so `⁅x_{0,last}(1), x_{last,1}(1)⁆` acts trivially.  Checked in
  `bh-met-92v/check.py`, check 3.
* The matrix model (`Ω = E_{n+1}(R)`, `St_n` acting through `stab`) satisfies `Agree` and
  `Mixed`, but freeness at `ω₀` is exactly injectivity of `stab`.  That is the open input,
  and it is circular.

**What is proved instead.**  The residual is `vdkOmegaBuild_Statement`.  It asks for the same
data, but replaces the family `vdkOmega_Mixed` (`n (n - 1) |R|²` permutation identities) by
**one** permutation identity `⁅x_{i₀,last}(1), x_{last,j₀}(1)⁆ = x_{i₀ j₀}(1)` at a single
index pair.  The reduction `vdkOmegaBuild_omegaStatement_of_statement` is proved from the
semidirect-product and Steinberg relators alone (`VdKOmegaBuildFull.lean`).

**LOUD: the residual is EQUIVALENT as a `Prop`, not strictly weaker.**  Both statements are
true (they are van der Kallen's theorem), so no true statement can be strictly weaker in the
logical sense.  `vdkOmegaBuild_statement_iff` proves the equivalence outright.  The residual is
strictly smaller in *proof content*: a constructor of `Ω` now has to check one commutator
identity instead of the whole mixed family.  It is not false: `vdkOmega_Statement` implies it.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- `vdkOmega_HasOmega n R` with the mixed family replaced by one identity at one index
pair. -/
def vdkOmegaBuild_HasOmegaOne (n : ℕ) (R : Type) [CommRing R] : Prop :=
  ∃ (Ω : Type) (α : vdkParPres_Tilde n R →* Equiv.Perm Ω)
    (β : vdkOmega_TildeMinus n R →* Equiv.Perm Ω) (ω₀ : Ω),
    vdkOmega_Agree α β ∧
      (∃ (i₀ j₀ : Fin n) (h : i₀ ≠ j₀), vdkOmegaBuild_MixedOne α β i₀ j₀ h) ∧
      ∀ g : St n R, α (vdkParPres_inr g) ω₀ = ω₀ → g = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_HasOmegaOne

theorem vdkOmegaBuild_hasOmega_of_hasOmegaOne {n : ℕ} {R : Type} [CommRing R] (hn : 3 ≤ n)
    (h : vdkOmegaBuild_HasOmegaOne n R) : vdkOmega_HasOmega n R := by
  obtain ⟨Ω, α, β, ω₀, hαβ, ⟨i₀, j₀, h0, hone⟩, hfree⟩ := h
  exact ⟨Ω, α, β, ω₀, hαβ, vdkOmegaBuild_mixed_of_mixedOne α β hαβ hn h0 hone, hfree⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_hasOmega_of_hasOmegaOne

/-- The converse (so the two are equivalent for `n ≥ 3`): take `i₀ = 0`, `j₀ = 1`. -/
theorem vdkOmegaBuild_hasOmegaOne_of_hasOmega {n : ℕ} {R : Type} [CommRing R] (hn : 2 ≤ n)
    (h : vdkOmega_HasOmega n R) : vdkOmegaBuild_HasOmegaOne n R := by
  obtain ⟨Ω, α, β, ω₀, hαβ, hmix, hfree⟩ := h
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun e ↦
    Nat.zero_ne_one (congrArg Fin.val e)
  have e := hmix _ _ h01 1 1
  rw [mul_one] at e
  exact ⟨Ω, α, β, ω₀, hαβ, ⟨_, _, h01, e⟩, hfree⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_hasOmegaOne_of_hasOmega

/-- **The residual.**  For every commutative ring `R` of stable rank `≤ r` there are a set `Ω`,
actions of the two parabolics agreeing on `St_{r+3}(R)`, and a point `ω₀` where `St_{r+3}(R)`
acts freely, such that ONE mixed identity `⁅x_{i₀,last}(1), x_{last,j₀}(1)⁆ = x_{i₀ j₀}(1)`
holds.  **Equivalent** to `vdkOmega_Statement` (`vdkOmegaBuild_statement_iff`), but smaller in
proof content. -/
def vdkOmegaBuild_Statement : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), vdkStab_StableRangeLE R r →
    vdkOmegaBuild_HasOmegaOne (r + 3) R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_Statement

/-- **Endpoint.**  The residual gives `vdkOmega_Statement`. -/
theorem vdkOmegaBuild_omegaStatement_of_statement (h : vdkOmegaBuild_Statement) :
    vdkOmega_Statement := by
  intro R _ r hr
  exact vdkOmegaBuild_hasOmega_of_hasOmegaOne (by omega) (h R r hr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_omegaStatement_of_statement

/-- **Endpoint.**  The residual gives `vdkParPres_NoHiddenRelStatement`. -/
theorem vdkOmegaBuild_noHiddenRelStatement_of_statement (h : vdkOmegaBuild_Statement) :
    vdkParPres_NoHiddenRelStatement :=
  vdkOmega_noHiddenRelStatement_of_statement (vdkOmegaBuild_omegaStatement_of_statement h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_noHiddenRelStatement_of_statement

/-- LOUD: the converse.  The residual is NOT strictly weaker as a `Prop`. -/
theorem vdkOmegaBuild_statement_of_omegaStatement (h : vdkOmega_Statement) :
    vdkOmegaBuild_Statement := by
  intro R _ r hr
  exact vdkOmegaBuild_hasOmegaOne_of_hasOmega (by omega) (h R r hr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_statement_of_omegaStatement

/-- LOUD: the residual is equivalent to `vdkOmega_Statement`. -/
theorem vdkOmegaBuild_statement_iff : vdkOmegaBuild_Statement ↔ vdkOmega_Statement :=
  ⟨vdkOmegaBuild_omegaStatement_of_statement, vdkOmegaBuild_statement_of_omegaStatement⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_statement_iff

end GroupApproximation.BooneHigman.Metabelian.ElemFP
