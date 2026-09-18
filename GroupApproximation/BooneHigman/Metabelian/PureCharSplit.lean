import GroupApproximation.BooneHigman.Metabelian.CoprimaryStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting the linearity of pure-characteristic pieces (lane bh-met-18)

`PureCharLinearityStatement` (`CoprimaryStatement`) is split by the two alternatives of
`IsPureCharacteristic Γ c`:

* `PureCharLinearityPrimeStatement`: `Γ` f.g. metabelian, `p` prime, `Γ'` killed by some `p ^ e`;
  then `Γ` embeds in `GL_d(K)` with `ringChar K = p`;
* `PureCharLinearityZeroStatement`: `Γ` f.g. metabelian, `Γ'` torsion-free; then `Γ` embeds in
  `GL_d(K)` with `ringChar K = 0`.

Endpoint: `pureCharLinearity_of_prime_zero`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- Linearity of f.g. metabelian groups whose derived subgroup has exponent a power of `p`. -/
def PureCharLinearityPrimeStatement : Prop :=
  ∀ (Γ : Type) [Group Γ], Group.FG Γ → IsMetabelianGroup Γ → ∀ p : ℕ, p.Prime →
    ∀ e : ℕ, (∀ x ∈ commutator Γ, x ^ (p ^ e) = 1) → ∃ (K : Type) (_ : Field K) (d : ℕ)
      (f : Γ →* Matrix.GeneralLinearGroup (Fin d) K), ringChar K = p ∧ Function.Injective f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.PureCharLinearityPrimeStatement

/-- Linearity of f.g. metabelian groups whose derived subgroup is torsion-free. -/
def PureCharLinearityZeroStatement : Prop :=
  ∀ (Γ : Type) [Group Γ], Group.FG Γ → IsMetabelianGroup Γ →
    (∀ x ∈ commutator Γ, ∀ n : ℕ, n ≠ 0 → x ^ n = 1 → x = 1) → ∃ (K : Type) (_ : Field K)
      (d : ℕ) (f : Γ →* Matrix.GeneralLinearGroup (Fin d) K),
      ringChar K = 0 ∧ Function.Injective f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.PureCharLinearityZeroStatement

/-- The linearity of pure-characteristic pieces from its prime and zero cases. -/
theorem pureCharLinearity_of_prime_zero (hp : PureCharLinearityPrimeStatement)
    (hz : PureCharLinearityZeroStatement) : PureCharLinearityStatement := by
  intro Γ _ hfg hG c hc
  rcases hc with ⟨rfl, htf⟩ | ⟨hc, e, he⟩
  · exact hz Γ hfg hG htf
  · exact hp Γ hfg hG c hc e he

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharLinearity_of_prime_zero

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
