import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Finiteness
import GroupApproximation.BooneHigman.Metabelian.PureCharSplit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeWreath
import GroupApproximation.Meta.AxiomGuard

/-!
# The prime case of pure-characteristic linearity: reduction to split extensions (lane bh-met-18)

Target `PureCharLinearityPrimeStatement` (`PureCharSplit`): a finitely generated metabelian group
`Γ` whose derived subgroup `Γ'` is killed by `p ^ e` embeds in `GL_d(K)` with `ringChar K = p`.

**Route (proved here).**  The extension `1 → Γ' → Γ → Γ ⧸ Γ' → 1` need not split.  The
Kaloujnine--Krasner embedding (`Envelope.exists_injective_regularWreath`) gives an injective
`κ : Γ →* B ⋊ Q` with `Q = Γ ⧸ Γ'` and `B = Q → Γ'` (translation action).  Both `B` and `Q` are
commutative (`Γ'' = 1`), and `B` is killed by `p ^ e` pointwise.  The subgroup
`H = κ(Γ) ⊔ Q` of `B ⋊ Q` is finitely generated, contains `Q`, and hence splits as
`(H ∩ B) ⋊ Q`.  A faithful representation of `H` restricts along `κ` to one of `Γ`.

**Remaining gap.** `PureCharPrimeSplitStatement`: a f.g. subgroup `H ≤ B ⋊ Q` with `B`, `Q`
commutative, `B` of exponent dividing `p ^ e`, and `Q ≤ H`, is linear over a field of
characteristic `p`.

* *True.*  `H` is f.g. metabelian (`H' ≤ (B ⋊ Q)' ≤ B` is abelian) and `H'` is killed by `p ^ e`,
  so `H` is an instance of `PureCharLinearityPrimeStatement`, which is Theorem 1.1 of Wehrfritz,
  Canad. J. Math. 27 (1975).  A direct route, for the record: `A = H ∩ B` is a f.g. module over the
  Noetherian ring `R = (ℤ/p^e)[Q]`; by Lasker--Noether it embeds in finitely many coprimary
  quotients; for a `P`-coprimary quotient, lifting a transcendence basis of `R/P` over `F_p`
  gives a subring `S ⊆ R` over which the quotient is `S ∖ pS`-torsion-free, so it embeds in its
  localization, a finite-length module over the truncated Cohen ring `C = S_{(p)}`; `C` embeds
  flatly in `W_e(k)` for `k` an algebraic closure of `Frac(S/p)`, and `H` then acts faithfully and
  `W_e(k)`-linearly on a finite `W_e(k)`-module (the affine module `A_C ⊕ C`), whose automorphism
  group acts faithfully on polynomial functions of bounded weighted degree in Witt coordinates, a
  finite-dimensional `k`-space; a faithful representation of the f.g. abelian group `Q` over `k`
  is added blockwise.
* *Strictly smaller in proof content.*  It is the special case of the target in which the group
  is split, `H = (H ∩ B) ⋊ Q` with `Q` a subgroup; the non-split extension, the
  Kaloujnine--Krasner construction, the commutativity of `Γ'` from `Γ'' = 1`, the exponent of the
  base, and finite generation of `H` are all proved here.

Endpoints: `pureCharLinearityPrime_of_split`, and `pureCharLinearity_of_split_zero` combining it
with `pureCharLinearity_of_prime_zero`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

open scoped commutatorElement

/-- **Split prime case.**  A finitely generated subgroup `H` of a semidirect product `B ⋊ Q` of
commutative groups, with `B` killed by `p ^ e` and `Q ≤ H`, is linear in characteristic `p`. -/
def PureCharPrimeSplitStatement : Prop :=
  ∀ (B Q : Type) [Group B] [Group Q] (φ : Q →* MulAut B), (∀ a b : B, a * b = b * a) →
    (∀ a b : Q, a * b = b * a) → ∀ p : ℕ, p.Prime → ∀ e : ℕ, (∀ b : B, b ^ (p ^ e) = 1) →
    ∀ H : Subgroup (B ⋊[φ] Q), H.FG → (SemidirectProduct.inr : Q →* B ⋊[φ] Q).range ≤ H →
      ∃ (K : Type) (_ : Field K) (d : ℕ) (f : H →* Matrix.GeneralLinearGroup (Fin d) K),
        ringChar K = p ∧ Function.Injective f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.PureCharPrimeSplitStatement

/-- In a metabelian group, elements of the derived subgroup commute. -/
theorem mul_comm_of_mem_commutator {Γ : Type*} [Group Γ] (hG : IsMetabelianGroup Γ) {x y : Γ}
    (hx : x ∈ commutator Γ) (hy : y ∈ commutator Γ) : x * y = y * x := by
  have h1 : ⁅x, y⁆ ∈ ⁅commutator Γ, commutator Γ⁆ := Subgroup.commutator_mem_commutator hx hy
  have hG' : ⁅commutator Γ, commutator Γ⁆ = ⊥ := hG
  rw [hG', Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.mul_comm_of_mem_commutator

/-- The quotient by the derived subgroup is commutative. -/
theorem quotient_commutator_mul_comm {Γ : Type*} [Group Γ] (a b : Γ ⧸ commutator Γ) :
    a * b = b * a :=
  mul_comm (a : Abelianization Γ) b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.quotient_commutator_mul_comm

/-- **Reduction of the prime case to split extensions**, by Kaloujnine--Krasner. -/
theorem pureCharLinearityPrime_of_split (h : PureCharPrimeSplitStatement) :
    PureCharLinearityPrimeStatement := by
  intro Γ _ hfg hG p hp e he
  haveI : Group.FG Γ := hfg
  obtain ⟨κ, hκ⟩ := Envelope.exists_injective_regularWreath (commutator Γ)
  have hB : ∀ a b : (Γ ⧸ commutator Γ) → ↥(commutator Γ), a * b = b * a := fun a b =>
    funext fun x => Subtype.ext (mul_comm_of_mem_commutator hG (a x).2 (b x).2)
  have hexp : ∀ b : (Γ ⧸ commutator Γ) → ↥(commutator Γ), b ^ (p ^ e) = 1 := fun b =>
    funext fun x => Subtype.ext (he _ (b x).2)
  obtain ⟨H, hH, hκH, hQH⟩ : ∃ H : Subgroup
      (Envelope.RegularWreath ↥(commutator Γ) (Γ ⧸ commutator Γ)), H.FG ∧ (∀ γ, κ γ ∈ H) ∧
      (SemidirectProduct.inr : (Γ ⧸ commutator Γ) →*
        Envelope.RegularWreath ↥(commutator Γ) (Γ ⧸ commutator Γ)).range ≤ H :=
    ⟨κ.range ⊔ (SemidirectProduct.inr : (Γ ⧸ commutator Γ) →*
        Envelope.RegularWreath ↥(commutator Γ) (Γ ⧸ commutator Γ)).range,
      Subgroup.FG.sup ((Group.fg_iff_subgroup_fg κ.range).mp (Group.fg_range κ))
        ((Group.fg_iff_subgroup_fg _).mp (Group.fg_range _)),
      fun γ => Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨γ, rfl⟩), le_sup_right⟩
  obtain ⟨K, _, d, ρ, hK, hρ⟩ := h _ _ (Envelope.shiftHom ↥(commutator Γ) (Γ ⧸ commutator Γ))
    hB quotient_commutator_mul_comm p hp e hexp H hH hQH
  refine ⟨K, inferInstance, d, ρ.comp (κ.codRestrict H hκH), hK, ?_⟩
  intro a b hab
  have hab' : ρ (κ.codRestrict H hκH a) = ρ (κ.codRestrict H hκH b) := hab
  exact hκ (congrArg Subtype.val (hρ hab'))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharLinearityPrime_of_split

/-- Linearity of pure-characteristic pieces from the split prime case and the zero case. -/
theorem pureCharLinearity_of_split_zero (hs : PureCharPrimeSplitStatement)
    (hz : PureCharLinearityZeroStatement) : PureCharLinearityStatement :=
  pureCharLinearity_of_prime_zero (pureCharLinearityPrime_of_split hs) hz

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharLinearity_of_split_zero

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
