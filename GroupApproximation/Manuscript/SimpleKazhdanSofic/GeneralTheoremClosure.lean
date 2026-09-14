import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainFromGeneral
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:general` and `thm:main`: the simplicity piece closed

`simple_kazhdan_sofic_group.tex` at 37551fd93, Theorem `thm:general` (tex l.109–127) and Theorem `thm:main`
(tex l.55–69, proved in tex l.238–271).

The assemblies `printedSimpleKazhdanGeneral_of_open_pieces` and `printedSimpleKazhdanSoficMain_of_open_pieces`
(`SimpleKazhdanSofic.MainFromGeneral`) consume three pieces.  This module closes the first:

* `printedGeneralSimplicityStatement`: section "Simplicity" (tex l.151–210), from skf-consequences'
  `General.isSimpleGroup_clopenGroupCrossedProduct_of_isOpen`, whose freeness hypothesis is the printed one.

It leaves exactly ms-core-3's two pieces open:

* `printedSimpleKazhdanGeneral_of_marked_limit`: `thm:general` from `PrintedMatricialMarkedLimitStatement`
  (section "Finite simple models", tex l.211–233);
* `printedSimpleKazhdanSoficMain_of_matricial_pieces`: `thm:main` from that piece and
  `PrintedPeriodicMatricialStatement` (tex l.244–271).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- **The simplicity piece, closed** (section "Simplicity", tex l.151–210), by skf-consequences'
`General.isSimpleGroup_clopenGroupCrossedProduct_of_isOpen`, whose freeness hypothesis is the printed one. -/
theorem printedGeneralSimplicityStatement : PrintedGeneralSimplicityStatement := by
  intro Λ _ _ Z _ _ _ _ _ _ _ _ hmin hfree n hn
  exact General.isSimpleGroup_clopenGroupCrossedProduct_of_isOpen hmin hfree hn

/-- **`thm:general` from the marked-limit piece** (ms-core-3). -/
theorem printedSimpleKazhdanGeneral_of_marked_limit (hmarked : PrintedMatricialMarkedLimitStatement) :
    PrintedSimpleKazhdanGeneral :=
  printedSimpleKazhdanGeneral_of_open_pieces printedGeneralSimplicityStatement hmarked

/-- **`thm:main` from ms-core-3's two pieces**: the marked limit and the periodic approximation. -/
theorem printedSimpleKazhdanSoficMain_of_matricial_pieces (hmarked : PrintedMatricialMarkedLimitStatement)
    (hper : PrintedPeriodicMatricialStatement) : PrintedSimpleKazhdanSoficMain :=
  printedSimpleKazhdanSoficMain_of_open_pieces printedGeneralSimplicityStatement hmarked hper

end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedGeneralSimplicityStatement
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedSimpleKazhdanGeneral_of_marked_limit
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedSimpleKazhdanSoficMain_of_matricial_pieces
