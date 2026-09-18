import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittETWOps
import GroupApproximation.Meta.AxiomGuard

/-!
# An invariant separating function space on `W_e(L)ⁿ` (bh-met-87h, part 11)

On `N = W_e(L)ⁿ`, with coordinates `(y i)_j` of weight `K ^ j`:

* every translation `x ↦ x + m` is weight-polynomial (`eHighWittE_isWeightPoly_trans`);
* in characteristic `p`, every matrix action `x ↦ (∑ₗ U i l * x l)ᵢ` is weight-polynomial
  (`eHighWittE_isWeightPoly_act`).

So `eHighWitt_exists_polyFun_of_weightPoly` (degree bound `K ^ e`) gives a finite-dimensional,
translation-stable, `U`-stable and separating space of functions `N → L`
(`eHighWittE_tw_polyFun`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

noncomputable section

variable {p : ℕ} [Fact p.Prime] {e : ℕ} {L : Type} [Field L] {n : ℕ}

theorem eHighWittE_isWeightPoly_trans (m : Fin n → TruncatedWittVector p e L) :
    eHighWitt_IsWeightPoly (eHighWittE_w p e n) (eHighWittE_co p e L n) (· + m) :=
  eHighWittE_isWeightPoly_of_good fun i =>
    eHighWittE_good_of_eq (eHighWittE_good_add (eHighWittE_good_coord i)
      (eHighWittE_good_const (m i))) fun x => (Pi.add_apply x m i).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_isWeightPoly_trans

theorem eHighWittE_isWeightPoly_act [CharP L p]
    (U : Fin n → Fin n → TruncatedWittVector p e L) :
    eHighWitt_IsWeightPoly (eHighWittE_w p e n) (eHighWittE_co p e L n)
      (fun x i => ∑ l, U i l * x l) :=
  eHighWittE_isWeightPoly_of_good fun i =>
    eHighWittE_good_sum Finset.univ (fun l x => U i l * x l) fun l _ =>
      eHighWittE_good_cmul (U i l) (eHighWittE_good_coord l)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_isWeightPoly_act

/-- **An invariant separating function space on `W_e(L)ⁿ`** for any family of matrices. -/
theorem eHighWittE_tw_polyFun [CharP L p] {Q : Type}
    (U : Q → Fin n → Fin n → TruncatedWittVector p e L) :
    ∃ V : Submodule L ((Fin n → TruncatedWittVector p e L) → L), FiniteDimensional L V ∧
      (∀ m : Fin n → TruncatedWittVector p e L, ∀ f ∈ V, (fun x => f (x + m)) ∈ V) ∧
      (∀ q : Q, ∀ f ∈ V, (fun x => f (fun i => ∑ l, U q i l * x l)) ∈ V) ∧
      (∀ m : Fin n → TruncatedWittVector p e L, m ≠ 0 → ∃ f ∈ V, f m ≠ f 0) :=
  eHighWitt_exists_polyFun_of_weightPoly (eHighWittE_w p e n)
    (fun v => (pow_ne_zero _ (eHighWittE_K_pos p e).ne' : eHighWittE_K p e ^ (v.2 : ℕ) ≠ 0))
    (eHighWittE_K p e ^ e)
    (fun v => (Nat.pow_le_pow_right (eHighWittE_K_pos p e) v.2.isLt.le :
      eHighWittE_K p e ^ (v.2 : ℕ) ≤ eHighWittE_K p e ^ e))
    (eHighWittE_co p e L n) (eHighWittE_co_injective p e L n)
    (fun q x i => ∑ l, U q i l * x l) (fun m => eHighWittE_isWeightPoly_trans m)
    (fun q => eHighWittE_isWeightPoly_act (U q))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_tw_polyFun

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
