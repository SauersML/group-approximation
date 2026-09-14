import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Meta.AxiomGuard

/-!
# `G_X` answers the questions of Brown, Ozawa and Pestov, closed

`simple_kazhdan_sofic_group.tex` at 8b36733d7, abstract l.33–36:

> So `G_X` is locally embeddable into finite groups, sofic and hyperlinear, which answers the question
> of Brown and Ozawa whether an infinite simple Kazhdan group can be hyperlinear, and Pestov's sofic
> version of it.

`ToeplitzAnswer.printedGXAnswersBrownOzawaPestov_of_main` derives the `G_X` form of the answer from
Theorem `thm:main`, at the Toeplitz subshift.  `thm:main` is closed
(`printedSimpleKazhdanSoficMain`), so the answer is closed along the printed route through `G_X`,
not through a different group.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- **`G_X` answers the questions** (abstract l.33–36): for some infinite minimal subshift `X`, the
group `G_X` is infinite, simple, Kazhdan, sofic and hyperlinear. -/
theorem printedGXAnswersBrownOzawaPestov : PrintedGXAnswersBrownOzawaPestov :=
  printedGXAnswersBrownOzawaPestov_of_main printedSimpleKazhdanSoficMain

end SimpleKazhdanSofic
end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedGXAnswersBrownOzawaPestov
