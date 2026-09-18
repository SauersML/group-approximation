import GroupApproximation.Manuscript.SimpleKazhdanSofic.Setting
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SturmianSubshiftMinimal
import GroupApproximation.Meta.AxiomGuard

/-!
# The Sturmian subshift in the shared setting of the note

`simple_kazhdan_sofic_group.tex` (origin/main e80dcf20a), tex l.261–264: "let $X_\alpha$ be the
infinite minimal Sturmian subshift [...]".

The note's main theorem and word-problem corollary state minimality through `IsMinimal` of
`SimpleKazhdanSofic.Setting`. This module shows that it agrees with `IsMinimalSubshift`, and states
and proves the printed sentence in that spelling, so that `sturmianSubshift α` instantiates the
main theorem's `X`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift

/-- The two spellings of minimality agree. -/
theorem isMinimalSubshift_iff_isMinimal {A : Type} [TopologicalSpace A] (S : Subshift A ℤ) :
    IsMinimalSubshift S ↔ IsMinimal S := by
  constructor
  · intro h C hC hsub hinv
    rcases Set.eq_empty_or_nonempty C with hempty | hne
    · exact Or.inl hempty
    · exact Or.inr (h C hsub hC hinv hne)
  · intro h Y hsub hY hinv hne
    exact (h Y hY hsub hinv).resolve_left hne.ne_empty

/-- Tex l.261–262, in the shared setting: for irrational `α ∈ (0,1)`, the Sturmian subshift is
infinite and minimal. -/
def PrintedSturmianSubshiftInfiniteIsMinimal : Prop :=
  ∀ α : ℝ, Irrational α → 0 < α → α < 1 →
    (sturmianSubshift α).carrier.Infinite ∧ IsMinimal (sturmianSubshift α)

/-- Tex l.261–262, closed, in the shared setting. -/
theorem printedSturmianSubshiftInfiniteIsMinimal : PrintedSturmianSubshiftInfiniteIsMinimal :=
  fun α hα hα0 hα1 =>
    ⟨sturmianSubshift_infinite α hα hα0 hα1,
      (isMinimalSubshift_iff_isMinimal (sturmianSubshift α)).mp
        (sturmianSubshift_isMinimal α hα hα0)⟩

#audit_axioms isMinimalSubshift_iff_isMinimal
#audit_closed_axioms printedSturmianSubshiftInfiniteIsMinimal

end SimpleKazhdanSofic
end GroupApproximation
