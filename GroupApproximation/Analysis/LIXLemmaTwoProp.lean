import GroupApproximation.CharClass.LemmaTwoStatement
import GroupApproximation.Analysis.LIXBlockProjections

/-!
# The single topological input of the STW Problem LIX endpoint

Everything the LIX counterexample needs from algebraic topology is one
proposition, and this module names it.

`LemmaTwoHolds` says that at **every** stage `j` of the tower the two rank-`(2+m)`
projections of the manuscript's Lemma 2 --- `F ⊕ H` and `𝟏² ⊕ H`, written
`CharClass.FHmat` and `CharClass.EHmat` --- are not Murray--von Neumann
equivalent as continuous fields over `M = S⁵ × ∏_j ℂP^{d_j}`.  Lane `cc-lix-odd`
proves it from Step A (`cs-clutching`), Step C (`cc-thom`) and Step D (`cc-wu`)
through `CharClass.not_continuousMvNEquiv`.

## Why it is a named `Prop` and why it lives here

Two reasons, and the second is the operational one.

**It is the seam.**  Above it, the C⋆-side is unconditional: the stage algebras,
the connecting maps, the inductive limit, its simplicity, and the reduction of
`¬ ProblemLIX` to one unitary are all proved outright.  Below it, the whole
characteristic-class layer --- mod-2 cohomology, Steenrod squares, the Thom
class, the Wu relation --- exists only to discharge this one statement.  Naming
it makes the dependency auditable from outside: `not_problemLIX_of_lemmaTwo`
takes exactly this and nothing else, so a reader can see what the topology is
for without reading any of it.

**It keeps the two halves buildable apart.**  `Manuscript/NinetyNineProblems/ProblemLIX.lean`
is root-wired, so anything it imports is a commitment of the root build.  This
module's import closure is deliberately small --- `CharClass/LemmaTwoStatement`
and its twelve dependencies, which contain **no** cohomology layer, plus
`Analysis/LIXBlockProjections` for `STW59.stageRank` --- so stating the endpoint
over `LemmaTwoHolds` does not put the root behind the characteristic-class
tower while that tower is still being built.

`Analysis/LIXBlockProjections` is imported rather than
`Analysis/LIXConnectingMapPoints`: `stageRank` is defined in the former
(`:447`), the latter reaches it only transitively, and the former's closure is
one module smaller.

## The dimensions

`lixDD j` is the manuscript's `(d_0, …, d_{j-1})` at stage `j`, namely
`d_i = r_i = 2^{i+1}`.  Every entry is even and positive, which is what Step D
needs --- `γ(V) = ∏_i (1 + h_i)^{d_i}` is supported in degrees `4k` exactly
because each `d_i` is even.  Nothing in this file uses that; it is recorded so
the choice of `stageRank` is visibly the one the parity argument wants.
-/

namespace GroupApproximation
namespace LIX

/-- The `ℂP` dimensions carried by stage `j` of the LIX tower: `d_i = 2^{i+1}`
for `i < j`. -/
def lixDD (j : ℕ) : Fin j → ℕ := fun i => STW59.stageRank (i : ℕ)

@[simp] theorem lixDD_apply (j : ℕ) (i : Fin j) : lixDD j i = 2 ^ ((i : ℕ) + 1) := rfl

/-- Every dimension is even, which is the hypothesis Step D of Lemma 2 runs on. -/
theorem even_lixDD (j : ℕ) (i : Fin j) : Even (lixDD j i) := by
  refine ⟨2 ^ (i : ℕ), ?_⟩
  rw [lixDD_apply, pow_succ]
  ring

/-- Every dimension is positive. -/
theorem lixDD_pos (j : ℕ) (i : Fin j) : 0 < lixDD j i := by
  rw [lixDD_apply]
  exact Nat.pow_pos (by norm_num)

/-- **Lemma 2 of the manuscript, at every stage of the LIX tower.**

The one topological input of the endpoint: over `M = S⁵ × ∏_{i<j} ℂP^{d_i}` the
projections `F ⊕ H` and `𝟏² ⊕ H` are not Murray--von Neumann equivalent as
continuous fields.  Both have pointwise rank `2 + m`, so this is not refutable
from the trace; it is the genuinely hard statement, and it is the only one the
C⋆-side takes on faith.

Proved by lane `cc-lix-odd` through `CharClass.not_continuousMvNEquiv`, from
Step A, Step C and Step D. -/
def LemmaTwoHolds : Prop :=
  ∀ j : ℕ, ¬ CharClass.ContinuousMvNEquiv
    (CharClass.FHmat (dd := lixDD j)) (CharClass.EHmat (dd := lixDD j))

theorem lemmaTwoHolds_iff :
    LemmaTwoHolds ↔ ∀ j : ℕ, ¬ CharClass.ContinuousMvNEquiv
      (CharClass.FHmat (dd := lixDD j)) (CharClass.EHmat (dd := lixDD j)) := Iff.rfl

/-- The stage-`j` instance of `LemmaTwoHolds`, which is the form a stage-level
argument consumes. -/
theorem LemmaTwoHolds.at_stage (h : LemmaTwoHolds) (j : ℕ) :
    ¬ CharClass.ContinuousMvNEquiv
      (CharClass.FHmat (dd := lixDD j)) (CharClass.EHmat (dd := lixDD j)) := h j

end LIX
end GroupApproximation
