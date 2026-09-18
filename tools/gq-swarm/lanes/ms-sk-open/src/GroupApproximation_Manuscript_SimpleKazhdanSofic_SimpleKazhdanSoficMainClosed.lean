import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanGeneralClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialEndpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:main`, closed

`simple_kazhdan_sofic_group.tex` at 37551fd93, Theorem `thm:main` (tex l.55–69):

> Let $X\subseteq A^{\Z}$ be an infinite minimal subshift over a finite alphabet, with shift $T$, and let
> $\LC(X,\F_2)$ be the ring of locally constant functions $X\to\F_2$. Then
> $G_X=\EL_3\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$ is an infinite, finitely generated, simple group with
> Kazhdan's property (T). It is the limit, in the space of marked groups, of finite simple groups
> $\SL_{3N}(\F_2)$ whose Cayley graphs, with respect to the images of a fixed generating set, form a
> family of expanders. So $G_X$ is locally embeddable into finite groups (LEF), sofic and hyperlinear.
> The same holds for $\EL_n\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$ for every $n\ge3$, with $\SL_{nN}(\F_2)$ in
> place of $\SL_{3N}(\F_2)$.

The note proves it through periodic approximations (tex l.238–271).  `printedSimpleKazhdanSoficMain_of_periodic`
(`SimpleKazhdanGeneralClosed`) derives it from the closed `thm:general` and the periodic approximation, and
ms-core-3's `printedPeriodicMatricialStatement` (`MatricialEndpoints`) supplies that approximation.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- **Theorem `thm:main`** (tex l.55–69): for every infinite minimal subshift `X` over a finite alphabet
and every `n ≥ 3`, `EL_n(LC(X, F₂) ⋊_T ℤ)` is infinite, finitely generated, simple and Kazhdan, a marked limit
of the finite simple groups `SL_{nN}(F₂)` whose Cayley graphs form expanders, and LEF, sofic and hyperlinear. -/
theorem printedSimpleKazhdanSoficMain : PrintedSimpleKazhdanSoficMain :=
  printedSimpleKazhdanSoficMain_of_periodic printedPeriodicMatricialStatement

end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSimpleKazhdanSoficMain
