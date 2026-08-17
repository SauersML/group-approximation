import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import GroupApproximation.Analysis.OmegaActionLinear
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

`mem_omegaFix_of_conjugated_fixed` carries the equality of the two
*projections* to the printed equality of the two *fixed spaces*,
`Fix π(sLs⁻¹) = Fix π(L)`.  That needs the identification of `ran P` with
`Fix π(L)` in both directions, and both directions are already in the corpus:
`OmegaActionLinear.omegaAct_proj_of_fixed` is `Fix ⊆ ran P`, whose spectral
content is the resolvent factorisation of `1 - P`, and
`kt_08_rep_mul_proj` is `ran P ⊆ Fix`.  So this half is an assembly too.

The result is exactly the `htransport` hypothesis of
`Analysis/CollapseUltraproductRepresentation.collapse_contradiction_kOmega`,
so `CO.21b` inside `K_ω` no longer carries an analytic hypothesis: the
Delorme–Guichardet step is proved, completeness of `K_ω` is proved, `π` is
built, and the transport step is this theorem.
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

/-! ## `Fix π(sLs⁻¹) = Fix π(L)`: the transport hypothesis, discharged -/

section Transport

variable (w : ℕ → ℝ)

/-- **The printed identification of the two fixed spaces.**  A vector of `K_ω`
fixed by every `π(s ι(γ) s⁻¹)` is fixed by every `π(ι γ)`.

This is the `htransport` hypothesis of
`Analysis/CollapseUltraproductRepresentation.collapse_contradiction_kOmega`
and of the corresponding step in `thm:kazhdan-transport`, and it is an
assembly of four results that were already in the corpus, in three lanes:

* `kt_19_omega_mem_fix_iff` turns the hypothesis into `V* η ∈ Fix`;
* `OmegaActionLinear.omegaAct_proj_of_fixed` — the printed `Fix ⊆ ran P`,
  whose spectral content is the resolvent factorisation of `1 - P` — turns
  that into `P (V* η) = V* η`;
* applying `V` and using `omegaConjProj_eq_proj`, the finiteness comparison
  proved above, replaces `V P V*` by `P` and gives `P η = η`;
* `kt_08_rep_mul_proj` — the printed `ran P ⊆ Fix`, i.e. `π(ι γ) P = P` —
  returns `η` to `Fix`.

The one-sided compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)` enters exactly once, inside
`omegaConjProj_eq_proj`, through `kt_09_conjugate_mul_proj`. -/
theorem mem_omegaFix_of_conjugated_fixed (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    {η : Vec Y w ω}
    (hη : ∀ γ : Γ, omegaAct Y w ω hw
      (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) η = η) :
    η ∈ omegaFix Y ω w hw D := by
  have hstar : omegaAct Y w ω hw (star D.shift) η ∈ omegaFix Y ω w hw D :=
    (kt_19_omega_mem_fix_iff Y ω w hw D η).1 hη
  have hproj : omegaAct Y w ω hw D.proj (omegaAct Y w ω hw (star D.shift) η)
      = omegaAct Y w ω hw (star D.shift) η :=
    OmegaActionLinear.omegaAct_proj_of_fixed Y w ω hw D
      ((mem_omegaFix_iff Y ω w hw D _).1 hstar)
  have hPη : omegaAct Y w ω hw D.proj η = η := by
    have h4 := congrArg (omegaAct Y w ω hw D.shift) hproj
    rw [← omegaAct_mul, ← omegaAct_mul, ← omegaAct_mul,
      shift_mul_proj_mul_star_shift_eq_proj Y ω D, D.shift_mul_star,
      omegaAct_one] at h4
    exact h4
  refine (mem_omegaFix_iff Y ω w hw D η).2 fun γ ↦ ?_
  have hrep : omegaRep Y ω D (D.iota γ) * D.proj = D.proj :=
    D.kt_08_rep_mul_proj γ
  calc omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ)) η
      = omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ))
          (omegaAct Y w ω hw D.proj η) := by rw [hPη]
    _ = omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ) * D.proj) η := by
          rw [omegaAct_mul]
    _ = omegaAct Y w ω hw D.proj η := by rw [hrep]
    _ = η := hPη

end Transport

end

end OmegaFiniteComparison
end GroupApproximation
