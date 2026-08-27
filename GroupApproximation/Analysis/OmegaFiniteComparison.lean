import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import GroupApproximation.Analysis.OmegaConjugationOperators
import GroupApproximation.Sofic.OmegaCoronaFinite

/-!
# `P = Q` in `B_ω`: the finiteness comparison of `lem:finitecompare`

The proof of `thm:projection-collapse` in `non_mf_groups_exist.tex` closes its
last paragraph with

> the projection `P` onto `Fix π(L)` and its conjugate `Q = π(s) P π(s)*`,
> whose range is `Fix π(sLs⁻¹)`, satisfy `P ≤ Q` and `P ∼ Q` in the norm
> ultraproduct, which is finite, so `P = Q` by Lemma `lem:finitecompare`

and `thm:kazhdan-transport` uses the same sentence.  Every input to it was
already in the corpus, in three different lanes, and no module had put them
together:

* `Analysis/OmegaConjugationOperators.omegaConjProj` is `Q = V P V*`, and
  `kt_21_omega_isometry_identities` is the Murray–von Neumann datum
  `r* r = Q`, `r r* = P` for `r = V* Q`;
* `Analysis/FiniteCStarMurrayVonNeumann.dedekindFiniteCStar_isometry_conjugate_eq_of_absorbs`
  is `lem:finitecompare` itself, in the form that consumes an isometry
  conjugate directly;
* `Sofic/OmegaCoronaFinite.omegaAdjointCorona_isDedekindFiniteMonoid` is the
  finiteness of `B_ω`, and `Sofic/OmegaOperatorUltraproduct` makes `B_ω` a
  `CStarAlgebra`, so both instance arguments are found by search.

So this file is one theorem and it is an assembly, not a construction: the
containment `P ≤ Q` enters as `kt_09_conjugate_mul_proj`, which is where the
printed one-sided compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)` is consumed, and the
conclusion is the printed `P = Q`.

## From `P = Q` to the fixed spaces

That step is **not** here.  `Analysis/OmegaFixRange` does it, and consumes
`omegaConjProj_eq_proj` below to do so: it identifies each fixed space with
the range of its projection (`range_proj_eq_omegaFix`,
`range_conjProj_eq_omegaFixConj`), rewrites one into the other along this
finiteness comparison (`omegaFixConj_eq_omegaFix`), and reads off the
implication the collapse endpoint consumes (`fix_of_fix_conjugated`).

This file deliberately stops at the algebra of `B_ω` and takes no import from
the `K_ω` action, so it stays validatable independently of that lane.
-/

namespace GroupApproximation
namespace OmegaFiniteComparison

open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection OmegaConjugationOperators

noncomputable section

variable {Γ H : Type} [Group Γ] [Group H]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)

/-- **`lem:finitecompare` applied to the transport pair.**  In `B_ω`, which is
a Dedekind-finite unital C*-algebra, the Kazhdan projection equals its own
conjugate by the implementer: `V P V* = P`.

The three inputs are exactly the printed ones — `P` is a projection
(`kt_08_*`), `V` is an isometry (`shift_star_mul`), and `P ≤ Q` holds in its
ring-theoretic form `Q P = P` (`kt_09_conjugate_mul_proj`, the one place the
one-sided compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)` is used).  Finiteness of `B_ω` and
its C*-structure are instances. -/
theorem omegaConjProj_eq_proj
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    omegaConjProj Y ω D = D.proj :=
  dedekindFiniteCStar_isometry_conjugate_eq_of_absorbs
    ⟨D.kt_08_proj_mul_proj, D.kt_08_isSelfAdjoint_proj⟩
    D.shift_star_mul D.kt_09_conjugate_mul_proj

/-- The same statement spelled out, so that it can be cited without unfolding
`omegaConjProj`. -/
theorem shift_mul_proj_mul_star_shift_eq_proj
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    D.shift * D.proj * star D.shift = D.proj :=
  omegaConjProj_eq_proj Y ω D

/-- **The implementer is the projection.**  With `P = Q`, the manuscript's
`r = V* Q` satisfies `r* r = P` and `r r* = P`, so the Murray–von Neumann
equivalence of `kt_21_omega_isometry_identities` collapses to an equality of
projections. -/
theorem omegaImplementer_isometry_identities_eq
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    star (omegaImplementer Y ω D) * omegaImplementer Y ω D = D.proj ∧
      omegaImplementer Y ω D * star (omegaImplementer Y ω D) = D.proj := by
  obtain ⟨h1, h2, -, -⟩ := kt_21_omega_isometry_identities Y ω D
  refine ⟨?_, h2⟩
  rw [h1]
  exact omegaConjProj_eq_proj Y ω D

end

end OmegaFiniteComparison
end GroupApproximation
