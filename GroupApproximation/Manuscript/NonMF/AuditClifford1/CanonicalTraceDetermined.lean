import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# The canonical trace is determined by its values on the canonical unitaries

`non_mf_groups_exist.tex`, lines 1827--1834:

> For a countable group $G$, let $u_g$ denote the canonical unitary in
> $C^*_{\max}(G)$.  The canonical trace $\tau_G$ is determined by
> \[ \tau_G(u_g)=\begin{cases}1,&g=1,\\0,&g\ne1.\end{cases} \]

The sentence says two things: `τ_G` takes the displayed values on the generators
`u_g = maximalGroupCStarGenerator G g`, and these values *determine* it. So every
continuous linear functional on `C*_max(G)` with the same values on the generators is
`τ_G`. The endpoint states both parts. Countability is not needed.

Proof route: the values come from `canonicalMaximalTrace_generator_one` and
`canonicalMaximalTrace_generator_of_ne_one`. Uniqueness is
`canonicalMaximalTrace_eq_of_generator`, which holds because the generators span a
dense subalgebra (`maximalGroupCStar_ext_of_generator_functional`).
-/

namespace GroupApproximation.Manuscript.NonMF.AuditClifford1

universe u

/-- tex 1827--1834: the canonical trace takes the value `1` on `u_1` and `0` on
`u_g` for `g ≠ 1`, and every continuous linear functional with these values equals
`τ_G`. -/
theorem manuscriptSentence_canonicalTraceDetermined (G : Type u) [Group G] :
    canonicalMaximalTrace G (maximalGroupCStarGenerator G 1) = 1 ∧
      (∀ g : G, g ≠ 1 → canonicalMaximalTrace G (maximalGroupCStarGenerator G g) = 0) ∧
      ∀ f : MaximalGroupCStar G →L[ℂ] ℂ,
        f (maximalGroupCStarGenerator G 1) = 1 →
          (∀ g : G, g ≠ 1 → f (maximalGroupCStarGenerator G g) = 0) →
            f = canonicalMaximalTrace G :=
  ⟨canonicalMaximalTrace_generator_one G,
    fun _ hg => canonicalMaximalTrace_generator_of_ne_one G hg,
    fun f h1 hne => canonicalMaximalTrace_eq_of_generator G f h1 hne⟩

#audit_axioms manuscriptSentence_canonicalTraceDetermined

end GroupApproximation.Manuscript.NonMF.AuditClifford1
