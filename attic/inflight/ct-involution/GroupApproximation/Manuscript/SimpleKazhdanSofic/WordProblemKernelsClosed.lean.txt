import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemKernels
import GroupApproximation.Manuscript.SimpleKazhdanSofic.StepanovSimplicity
import GroupApproximation.Meta.AxiomGuard

/-!
# Different subshifts give different kernels: closed (simple_kazhdan_sofic_group.tex, after cor:wp)

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, "Word problems and factors" (census key
`bdd19b7d1e1f`, tex l.541–544):

> For a fixed alphabet, every $G_X$ is a simple quotient of the Kazhdan group $\EL_3(F)$, and
> $e_{12}(\prod_{t<m}\tau_-^t\tau_{v_t}\tau_+^t)$ lies in the kernel if and only if $v\notin L(X)$, so
> different subshifts give different kernels.

`printedWordProblemKernels_of_simplicity` (WordProblemKernels) proves the paragraph over the simplicity
statement of `thm:main`; sk-stepanov's `printedSimplicityStatement_stepanov` (StepanovSimplicity) proves
that statement.

* `printedWordProblemKernels : PrintedWordProblemKernels`.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

/-- **"For a fixed alphabet, every $G_X$ is a simple quotient of the Kazhdan group $\EL_3(F)$ [...] so
different subshifts give different kernels"** (tex l.541–544), closed. -/
theorem printedWordProblemKernels : PrintedWordProblemKernels :=
  printedWordProblemKernels_of_simplicity printedSimplicityStatement_stepanov

end SimpleKazhdanSofic

end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedWordProblemKernels
