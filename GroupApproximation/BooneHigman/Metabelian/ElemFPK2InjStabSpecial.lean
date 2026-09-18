import GroupApproximation.BooneHigman.Metabelian.ElemFPK2InjStabRetract
import GroupApproximation.Meta.AxiomGuard

/-!
# Injective `K₂` stability for `F_p[s_1, …, s_k]`: reduction to elements that die under every
specialization to fewer variables

Lane `bh-met-80`.  Target: `VdKRowParInjK2StabStatement` (module `ElemFPK2VdKRowParInjEndpoint`):
for `p` prime and `k > 0`, `K2Stab (k + 4)` is injective over `R_k = F_p[s_1, …, s_k]`.

## The isolated statement

`K2InjStabSpecializationStatement`: for `p` prime, `k ≥ 0`, `N ≥ k + 4`, `N ≥ 5`, an element
`u ∈ K₂(N, R_k)` with `K2Stab N u = 1` is trivial, **provided** `K2Map ψ u = 1` for every
`j < k` and every ring map `ψ : R_k →+* R_j`.  This is `PolyK2InjectiveStabilityStatement`
with one extra hypothesis on `u`, so each instance is weaker.  The extra hypothesis is not
vacuous.  For `j = 0` it contains evaluation at every `F_p`-point, in particular `ev₀`.  For
`j = k - 1` it contains every substitution of one variable by a polynomial in the others.

## What is proved

* `k2InjStab_polyInjective_of_specialization`: the isolated statement gives
  `PolyK2InjectiveStabilityStatement`, by strong induction on the number `k` of variables at a
  fixed rank `N`.  Given `u` with `K2Stab N u = 1` and `ψ : R_k → R_j`, `j < k`, naturality
  (`k2InjStab_K2Stab_K2Map`) gives `K2Stab N (ψ u) = ψ (K2Stab N u) = 1`.  Since
  `N ≥ k + 4 > j + 4`, the induction hypothesis at `j` gives `ψ u = 1`.  So the extra
  hypothesis holds automatically, and the isolated statement gives `u = 1`.
* `k2InjStab_target_of_specialization`, `k2InjStab_vdkRowParInjective_of_specialization`: the
  endpoints, `→ VdKRowParInjK2StabStatement` and `→ VdKRowParInjectiveStatement`.
* `k2InjStab_specialization_of_target`: the converse, via `k2InjStab_polyInjective_of_target`.
* `k2InjStab_specialization_of_nilPos_of_fieldStab`: the existing `ker ev₀` gap
  `PolyK2NilStabilityPosStatement`, together with **injective stability** (not vanishing) of
  `K₂(N, F_p)` for `N ≥ 5`, gives the isolated statement.  For `k > 0` the extra hypothesis
  with `ψ = C ∘ ev₀` gives `ev₀ u = 1` (`k2InjStab_constantCoeff_eq_one`).  For `k = 0` the
  isolated statement is exactly field injective stability.  So the isolated statement is no
  stronger than the existing pair of gaps.  The previous route needed field *vanishing*
  (`FieldK2VanishingStatement`); here only field injective stability appears.

## LOUD: strength

The isolated statement is **provably equivalent** to the target: both directions are proved
here.  The previous lane's cuts were equivalent in the same sense.  It is weaker instancewise:
same quantifiers as `PolyK2InjectiveStabilityStatement`, plus an extra hypothesis on `u`.  It is
strictly smaller in proof content: the induction on the number of variables, the rank
parameter and the naturality bookkeeping are discharged.  What a proof must still supply is
injective stability on the elements that die under every specialization to fewer variables,
including the field case `k = 0`.

## LOUD: the suggested ring-independent cut (a) is false as stated

"Transitivity of `E(n+1, R)` on unimodular rows implies injectivity of `K₂(n, R) → K₂(n+1, R)`"
is not a ring-independent implication.  Over any field `F`, `E(3, F)` is transitive on
unimodular rows of length `3`.  But `K₂(2, ℝ) → K₂(3, ℝ)` is not injective: by Matsumoto and
Suslin, `K₂(2, F) = K₂Sp(F)` maps onto `K₂(F)` with kernel `I³(F)`, and `I³(ℝ) ≅ ℤ`.  This is
a literature remark only; no Lean depends on it.  Any true ring-independent reduction must
carry van der Kallen's stabilizer or cocycle data, which is equivalent to the target: it is
`VdKRowData`, module `ElemFPK2VdKAssemble`.  So cut (a) was not taken.

## Truth check

The isolated statement is implied by `PolyK2InjectiveStabilityStatement`
(`k2InjStab_specialization_of_polyInjective`).  That statement is true: `R_k` is noetherian of
Krull dimension `k`, so Bass gives `sr(R_k) ≤ k + 1`.  Van der Kallen's injective stability
gives injectivity of `K₂(n) → K₂(n+1)` for `n ≥ sr + 2`, which covers `N ≥ k + 4`.  For `k = 0`,
`F_p` has `sr = 1` and `N ≥ 5 ≥ 3`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The isolated gap.**  Injective stability of `K₂(N, F_p[s_1, …, s_k])` (`N ≥ k + 4`,
`N ≥ 5`) for elements that die under every ring map to a polynomial ring in fewer variables.
Instancewise weaker than `PolyK2InjectiveStabilityStatement`.  LOUD: provably equivalent to
`VdKRowParInjK2StabStatement`, see the module docstring. -/
def K2InjStabSpecializationStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, k + 4 ≤ N → 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)),
      (∀ j : ℕ, j < k →
        ∀ ψ : MvPolynomial (Fin k) (ZMod p) →+* MvPolynomial (Fin j) (ZMod p),
          K2Map ψ u = 1) →
      K2Stab N (MvPolynomial (Fin k) (ZMod p)) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2InjStabSpecializationStatement
