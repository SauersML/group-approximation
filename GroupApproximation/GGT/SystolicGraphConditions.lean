import GroupApproximation.GGT.SystolicDefs

/-!
# Metric conditions on the one-skeleton of a systolic complex

Four properties of a simple graph, stated with the path metric `SimpleGraph.dist`.  The disc
lemmas of `GGT/SystolicProjection` produce them for the one-skeleton of a simply connected
triangle complex with 6-large links; the dismantling of intersections of balls consumes them.

* `ProjectionClique G`: for every base vertex `o`, the neighbours of `u` one step closer to
  `o` are pairwise adjacent.
* `TriangleCondition G`: two adjacent vertices at the same positive distance from `o` have a
  common neighbour one step closer to `o`.
* `NoInducedFourCycle G`, `NoInducedFiveCycle G`: every cycle of length four or five through
  distinct vertices has a chord.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic

variable {V : Type*}

/-- **Projection clique**: for every base vertex `o`, the neighbours of `u` one step closer to
`o` are pairwise adjacent. -/
def ProjectionClique (G : SimpleGraph V) : Prop :=
  ∀ o u x y : V, G.Adj u x → G.Adj u y → G.dist o x + 1 = G.dist o u →
    G.dist o y + 1 = G.dist o u → x ≠ y → G.Adj x y

/-- **Triangle condition**: two adjacent vertices at the same positive distance from `o` have a
common neighbour one step closer to `o`. -/
def TriangleCondition (G : SimpleGraph V) : Prop :=
  ∀ o u v : V, G.Adj u v → G.dist o u = G.dist o v → 0 < G.dist o u →
    ∃ c : V, G.Adj u c ∧ G.Adj v c ∧ G.dist o c + 1 = G.dist o u

/-- **No induced four-cycle**: a cycle `a b c d` through distinct vertices has a chord. -/
def NoInducedFourCycle (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d →
    G.Adj a c ∨ G.Adj b d

/-- **No induced five-cycle**: a cycle `a b c d e` through distinct vertices has a chord. -/
def NoInducedFiveCycle (G : SimpleGraph V) : Prop :=
  ∀ a b c d e : V, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e a →
    a ≠ c → a ≠ d → b ≠ d → b ≠ e → c ≠ e →
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b d ∨ G.Adj b e ∨ G.Adj c e

end Systolic
end GroupApproximation
