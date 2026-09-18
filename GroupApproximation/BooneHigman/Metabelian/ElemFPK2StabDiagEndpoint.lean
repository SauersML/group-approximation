import GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagAction
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabRange
import GroupApproximation.Meta.AxiomGuard

/-!
# The diagonal stability gap as a van der Kallen action

Lane `bh-met-35`.  Write `R_k = F_p[s_1..s_k]`.  This module reduces `PolyK2StabRangeDiagStatement`
(module `ElemFPK2StabRange`) to `StabDiagLastRootActionStatement`.  The new statement asks, for `p`
prime and `k ≥ 1`, for three things:

* a set `Ω` with an action of `St_{k+4}(R_k)`;
* permutations `T` for the roots of `St_{k+5}(R_k)`, agreeing with the action on the old roots and
  satisfying every Steinberg relator that involves the new index `k + 4`;
* a point `ω₀` whose stabilizer meets `ker(ev₀) ∩ K₂(k+4, R_k)` only in `1`.

Endpoints:

* `polyK2StabRangeDiag_of_lastRootAction`: the action statement implies the diagonal gap.  This is
  `eq_one_of_K2Stab_of_lastRootAction` with `P = ker ev₀`.
* `stabDiagLastRootAction_of_polyK2StabRangeDiag`: the converse.  Take `Ω = St_{k+5}(R_k)` with
  left multiplication through `stab`, and `ω₀ = 1`.

**LOUD: the two statements are logically equivalent**, and both directions are proved here.  The
new statement is not logically weaker.  It is strictly smaller in *proof content*.  The reduction
removes every formal part of the permutation-action method:

* the passage from generators to a homomorphism `St_{k+5}(R_k) →* Perm Ω`
  (`PresentedGroup.toGroup`);
* all Steinberg relators on roots avoiding the new index (from `compat` and the relations of
  `St_{k+4}`);
* the comparison `lift ∘ stab = act`, and the fixed-point argument.

What remains is the mathematical core of van der Kallen's proof:

* the construction of `Ω`, in his proof built from `St_{k+4}(R_k)` and unimodular columns, using
  the stable range of `R_k`;
* the relators that involve the new index;
* separation of `ω₀` on `ker ev₀`.

The converse shows that the demand is satisfiable, but only by assuming the gap, so it gives no
proof of the gap.

Truth.  By the converse, the statement follows from `PolyK2StabRangeDiagStatement`.  That statement
is true: by Bass, `sr(R_k) ≤ k + 1`, and van der Kallen's injective stability holds for `n ≥ sr + 2`,
while here `n = k + 4 ≥ sr + 3`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- Left multiplication of `St_{n+1}(R)` on itself. -/
def stabDiagLeftPerm (n : ℕ) (R : Type*) [Ring R] : St (n + 1) R →* Equiv.Perm (St (n + 1) R) :=
  MulAction.toPermHom (St (n + 1) R) (St (n + 1) R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagLeftPerm

/-- The left-regular `LastRootAction`: `St_n(R)` acts on `St_{n+1}(R)` by left multiplication
through `stab`, and `T` is left multiplication by the roots. -/
def stabDiagLeftRegular (n : ℕ) (R : Type*) [Ring R] : LastRootAction n R (St (n + 1) R) where
  act := (stabDiagLeftPerm n R).comp (stab n R)
  T i j hij a := stabDiagLeftPerm n R (x i j hij a)
  compat i j hij h' a := by
    change stabDiagLeftPerm n R (x i.castSucc j.castSucc h' a) =
      stabDiagLeftPerm n R (stab n R (x i j hij a))
    rw [stab_x]
  add i j hij a b _ := by
    change stabDiagLeftPerm n R (x i j hij a) * stabDiagLeftPerm n R (x i j hij b) =
      stabDiagLeftPerm n R (x i j hij (a + b))
    rw [← map_mul, x_mul]
  commute i j k l hij hkl hjk hli a b _ := by
    change ⁅stabDiagLeftPerm n R (x i j hij a), stabDiagLeftPerm n R (x k l hkl b)⁆ = 1
    rw [← map_commutatorElement, (x_commute_of_ne i j k l hij hkl hjk hli a b).commutator_eq,
      map_one]
  adjacent i j k hij hjk hik a b _ := by
    change ⁅stabDiagLeftPerm n R (x i j hij a), stabDiagLeftPerm n R (x j k hjk b)⁆ =
      stabDiagLeftPerm n R (x i k hik (a * b))
    rw [← map_commutatorElement, x_commutator i j k hij hjk hik a b]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagLeftRegular

/-- **The remaining gap**: a van der Kallen action for the diagonal case `N = k + 4`, `k ≥ 1`, of
injective stability on the kernel of `ev₀`.  Logically equivalent to
`PolyK2StabRangeDiagStatement` (see the module docstring), with the formal part of the method
removed. -/
def StabDiagLastRootActionStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 0 < k →
    ∃ (Ω : Type) (A : LastRootAction (k + 4) (MvPolynomial (Fin k) (ZMod p)) Ω) (ω₀ : Ω),
      ∀ u : K2n (k + 4) (MvPolynomial (Fin k) (ZMod p)),
        K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p) u = 1 →
          A.act (u : St (k + 4) (MvPolynomial (Fin k) (ZMod p))) ω₀ = ω₀ → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.StabDiagLastRootActionStatement

/-- The van der Kallen action statement gives the diagonal stability gap. -/
theorem polyK2StabRangeDiag_of_lastRootAction (h : StabDiagLastRootActionStatement) :
    PolyK2StabRangeDiagStatement := by
  intro p hp k hk u hu0 hu
  obtain ⟨Ω, A, ω₀, hsep⟩ := h p hp k hk
  exact eq_one_of_K2Stab_of_lastRootAction A
    (fun v ↦ K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p) v = 1)
    ω₀ hsep u hu0 hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2StabRangeDiag_of_lastRootAction

/-- Converse (truth check): the diagonal stability gap gives the action statement, through the
left-regular action. -/
theorem stabDiagLastRootAction_of_polyK2StabRangeDiag (h : PolyK2StabRangeDiagStatement) :
    StabDiagLastRootActionStatement := by
  intro p hp k hk
  refine ⟨St (k + 4 + 1) (MvPolynomial (Fin k) (ZMod p)),
    stabDiagLeftRegular (k + 4) (MvPolynomial (Fin k) (ZMod p)), 1, ?_⟩
  intro u hu0 hfix
  refine h p hp k hk u hu0 (Subtype.ext ?_)
  have h1 : stab (k + 4) (MvPolynomial (Fin k) (ZMod p))
      (u : St (k + 4) (MvPolynomial (Fin k) (ZMod p))) * 1 = 1 := hfix
  rw [mul_one] at h1
  exact h1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagLastRootAction_of_polyK2StabRangeDiag

/-- **Combined endpoint**: the action statement, the nil gap and the field case give
`K₂(N, F_p[s_1..s_k]) = 0` for `N ≥ k + 4`, `N ≥ 5`. -/
theorem polynomialFpK2Vanishing_of_lastRootAction (hact : StabDiagLastRootActionStatement)
    (hnil : PolyK2NilPosStatement) (hfield : FieldK2VanishingStatement) :
    PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_stabRangeDiag (polyK2StabRangeDiag_of_lastRootAction hact) hnil hfield

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polynomialFpK2Vanishing_of_lastRootAction

end GroupApproximation.BooneHigman.Metabelian.ElemFP
