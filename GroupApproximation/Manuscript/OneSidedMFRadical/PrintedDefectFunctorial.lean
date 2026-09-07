import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation

/-!
# `eq:defect-functorial`

`non_mf_groups_exist.tex`, the displayed inequality that follows
`eq:intrinsic-defect`:

> For every homomorphism `f : G → H`,
> `f(𝔇_G(L)) ≤ 𝔇_H(f(L))`,
> since compressors, centralizing elements, and commutators of `L` map to
> compressors, centralizing elements, and commutators of `f(L)`, and conjugates
> map to conjugates.

The manuscript now cites this display where it used to cite
`lem:commutator-in-defect`, so the display needs a **closed named proposition**
of its own.

## Nothing new is proved here

The inequality is already a theorem of this repository:
`OneSidedMFRadical.map_printedDefect_le` in
`Manuscript.OneSidedMFRadical.DefectSaturation`, whose proof is the printed
one clause for clause — `map_mem_printedCompressionSet` for the compressors,
`Commute.map` for the centralizing elements, `map_commutatorElement` for the
commutators, and `Subgroup.normalClosure_le_normal` for *conjugates map to
conjugates*.  This module only wraps it as the closed proposition the printed
display deserves, so that a consumer can cite `eq:defect-functorial` by name
and the axiom audit can see it.

Restating the proof here would have made a second, differently named copy of a
theorem the repository already has.  The one thing worth changing in the older
module is its docstring, which calls the display `eq:defect-functoriality`; the
committed tex labels it `eq:defect-functorial`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-- **`eq:defect-functorial`, as one closed proposition.**

> For every homomorphism `f : G → H`, `f(𝔇_G(L)) ≤ 𝔇_H(f(L))`.

`f(𝔇_G(L))` is `(printedDefect L).map f` and `f(L)` is `L.map f`, so the
display is literally the inequality below.  No hypothesis on `f`: it is an
arbitrary homomorphism, neither injective nor surjective, which is what the
proof of `thm:torsion-free` needs when it applies the display to the saturation
quotient map. -/
def PrintedDefectFunctorial : Prop :=
  ∀ (G H : Type) [Group G] [Group H] (f : G →* H) (L : Subgroup G),
    (printedDefect L).map f ≤ printedDefect (L.map f)

/-- **`eq:defect-functorial`, proved.**  The content is
`DefectSaturation.map_printedDefect_le`, which this repository has carried since
the defect-saturation lane; the display is that theorem with its group
arguments universally quantified inside the proposition. -/
theorem manuscriptPrintedDefectFunctorial : PrintedDefectFunctorial := by
  intro G H _ _ f L
  exact map_printedDefect_le f L

end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedDefectFunctorial
