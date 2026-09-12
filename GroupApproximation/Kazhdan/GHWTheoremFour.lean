import GroupApproximation.Kazhdan.GHWFiniteReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# GHW Theorem 4: countable subgroups of `GL_2` over a field

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring` (tex lines 1146--1147):

> Every countable subgroup of `GL_2` over a field has the Haagerup property~[GHW, Theorem 4], …

`PrintedGHWTheoremFour` is this sentence at the printed generality: every field `K` and every
countable subgroup `Γ ≤ GL_2(K)`.

## The union

By `hasHaagerupProperty_of_closure_finite` it is enough that every subgroup of `GL_2(K)` generated
by a finite set has the Haagerup property.  A field has prime characteristic or characteristic
zero (`CharP.char_is_prime_or_zero` at `ringChar K`), so the finitely generated case splits into

* `GHWFinitelyGeneratedCharP`: fields of prime characteristic `p` (module `GHWCharP`,
  `hasHaagerupProperty_closure_of_charP`);
* `GHWFinitelyGeneratedCharZero`: fields of characteristic zero (module `GHWCharZero`,
  `hasHaagerupProperty_closure_of_charZero`).

`printedGHWTheoremFour_of_charP_charZero` is the union.  The closed endpoint
`printedGHWTheoremFour` follows from it once both cases are on main.

## Manuscript status

Tex 1146--1147, first clause: `partial` (the union over the two finitely generated cases).
-/

namespace GroupApproximation
namespace GHW

open Haagerup

/-- **GHW Theorem 4, printed (tex 1146--1147).**  "Every countable subgroup of
$\mathrm{GL}_2$ over a field has the Haagerup property~\cite[Theorem~4]{GHW}."  Fields range over
`Type`. -/
def PrintedGHWTheoremFour : Prop :=
  ∀ (K : Type) [Field K] (Γ : Subgroup (GL (Fin 2) K)), Countable Γ →
    HasHaagerupProperty.{0, 0} Γ

/-- **Prime characteristic, finitely generated subgroups.** -/
def GHWFinitelyGeneratedCharP : Prop :=
  ∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (s : Set (GL (Fin 2) F)), s.Finite →
    HasHaagerupProperty.{0, 0} (Subgroup.closure s)

/-- **Characteristic zero, finitely generated subgroups.** -/
def GHWFinitelyGeneratedCharZero : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)), s.Finite →
    HasHaagerupProperty.{0, 0} (Subgroup.closure s)

/-- **Finitely generated subgroups, every field.**  The characteristic of a field is prime or zero,
so the two finitely generated cases cover every field. -/
theorem hasHaagerupProperty_closure_of_charP_charZero (hp : GHWFinitelyGeneratedCharP)
    (h0 : GHWFinitelyGeneratedCharZero) (K : Type) [Field K] (s : Set (GL (Fin 2) K))
    (hs : s.Finite) : HasHaagerupProperty.{0, 0} (Subgroup.closure s) := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
  · haveI : Fact (ringChar K).Prime := ⟨hprime⟩
    exact hp K (ringChar K) s hs
  · haveI : CharP K 0 := ringChar.of_eq hzero
    haveI : CharZero K := CharP.charP_to_charZero K
    exact h0 K s hs

/-- **The union.**  GHW Theorem 4 from its finitely generated cases in prime characteristic and in
characteristic zero. -/
theorem printedGHWTheoremFour_of_charP_charZero (hp : GHWFinitelyGeneratedCharP)
    (h0 : GHWFinitelyGeneratedCharZero) : PrintedGHWTheoremFour := by
  intro K _ Γ hΓ
  exact @hasHaagerupProperty_of_closure_finite (GL (Fin 2) K) _ Γ hΓ
    (hasHaagerupProperty_closure_of_charP_charZero hp h0 K)

end GHW
end GroupApproximation

#audit_axioms GroupApproximation.GHW.PrintedGHWTheoremFour
#audit_axioms GroupApproximation.GHW.GHWFinitelyGeneratedCharP
#audit_axioms GroupApproximation.GHW.GHWFinitelyGeneratedCharZero
#audit_axioms GroupApproximation.GHW.hasHaagerupProperty_closure_of_charP_charZero
#audit_axioms GroupApproximation.GHW.printedGHWTheoremFour_of_charP_charZero
