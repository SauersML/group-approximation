import GroupApproximation.Dynamics.SubshiftWordGraph
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Topology.Clopen

/-!
# The defect of a noncyclic edge

sec:chain-core, proof of lem:chain-core-models.  "A noncyclic edge `a → b` gives a forward-closed set
of vertices: those reachable from `b`, which excludes `a`.  Its cylinder union `P` satisfies
`T(P) ⊆ P`.  If `x` starts with that edge, then `Tx ∈ P ∖ T(P)`."

Here `T = shift 1`, so `(T x) i = x (1 + i)`.  An edge of the level-`r` word graph is a word
`w ∈ language X (r + 1)`, from `Fin.init w` to `Fin.tail w`; it is noncyclic when `Fin.tail w` does
not reach `Fin.init w`.  The cylinder union of the vertices reachable from `b` is the set
`reachableCylinderUnion X r b` of points of `X` whose word `x[0, r)` is reachable from `b`.

## Main results
* `not_reflTransGen_of_not_isCyclicEdge`: the vertices reachable from `b` exclude `a`.
* `isClosed_reachableCylinderUnion`, `reachableCylinderUnion_eq_inter`: `P` is `X` intersected with
  a clopen set.
* `mapsTo_shift_reachableCylinderUnion`: `T(P) ⊆ P`.
* `shift_mem_diff_of_not_isCyclicEdge`: if `x` starts with the noncyclic edge, `Tx ∈ P ∖ T(P)`.
* `diff_image_shift_nonempty_of_not_isCyclicEdge`: in particular `P ∖ T(P)` is nonempty.
-/

namespace GroupApproximation.ChainCore

open Set SymbolicDynamics.FullShift GroupApproximation.WordGraph

variable {A : Type*}

/-- The cylinder union `P` of the vertices reachable from `b` in the level-`r` word graph: the points
of `X` whose word on `[0, r)` is reachable from `b`. -/
def reachableCylinderUnion (X : Set (ℤ → A)) (r : ℕ) (b : Fin r → A) : Set (ℤ → A) :=
  {x | x ∈ X ∧ Relation.ReflTransGen (wordEdge X r) b (word x 0 r)}

theorem shift_one_injective : Function.Injective (shift (A := A) (1 : ℤ)) := fun x y h => by
  funext i
  have hi := congrFun h (i - 1)
  simp only [shift_apply] at hi
  rwa [show (1 : ℤ) + (i - 1) = i by omega] at hi

/-- sec:chain-core: the vertices reachable from the target `b` of a noncyclic edge `a → b` exclude
its source `a`. -/
theorem not_reflTransGen_of_not_isCyclicEdge {X : Set (ℤ → A)} {r : ℕ} {w : Fin (r + 1) → A}
    (hw : w ∈ language X (r + 1)) (hnc : ¬ IsCyclicEdge X r w) :
    ¬ Relation.ReflTransGen (wordEdge X r) (Fin.tail w) (Fin.init w) :=
  fun h => hnc ⟨hw, h⟩

/-- The set of configurations whose word on `[0, r)` lies in a given set is clopen. -/
theorem isClopen_setOf_word_mem [TopologicalSpace A] [DiscreteTopology A] (r : ℕ)
    (S : Set (Fin r → A)) : IsClopen {x : ℤ → A | word x 0 r ∈ S} :=
  (isClopen_discrete S).preimage (continuous_pi fun _ => continuous_apply _)

theorem reachableCylinderUnion_eq_inter (X : Set (ℤ → A)) (r : ℕ) (b : Fin r → A) :
    reachableCylinderUnion X r b =
      X ∩ {x : ℤ → A | word x 0 r ∈ {u | Relation.ReflTransGen (wordEdge X r) b u}} :=
  rfl

theorem isClosed_reachableCylinderUnion [TopologicalSpace A] [DiscreteTopology A]
    {X : Set (ℤ → A)} (hXc : IsClosed X) (r : ℕ) (b : Fin r → A) :
    IsClosed (reachableCylinderUnion X r b) := by
  rw [reachableCylinderUnion_eq_inter]
  exact hXc.inter (isClopen_setOf_word_mem r _).isClosed

/-- sec:chain-core: the cylinder union `P` of a forward-closed set of vertices satisfies
`T(P) ⊆ P`. -/
theorem mapsTo_shift_reachableCylinderUnion {X : Set (ℤ → A)}
    (hX : ∀ n : ℤ, MapsTo (shift n) X X) (r : ℕ) (b : Fin r → A) :
    MapsTo (shift 1) (reachableCylinderUnion X r b) (reachableCylinderUnion X r b) := by
  rintro x ⟨hx, hb⟩
  refine ⟨hX 1 hx, ?_⟩
  have h1 := wordEdge_word hX hx 0 r
  rw [zero_add] at h1
  rw [word_shift, add_zero]
  exact hb.tail h1

/-- sec:chain-core: if `x` starts with a noncyclic edge `w`, then `Tx ∈ P ∖ T(P)` for the cylinder
union `P` of the vertices reachable from `Fin.tail w`. -/
theorem shift_mem_diff_of_not_isCyclicEdge {X : Set (ℤ → A)}
    (hX : ∀ n : ℤ, MapsTo (shift n) X X) {r : ℕ} {w : Fin (r + 1) → A}
    (hw : w ∈ language X (r + 1)) (hnc : ¬ IsCyclicEdge X r w) {x : ℤ → A} (hx : x ∈ X)
    (hxw : word x 0 (r + 1) = w) :
    shift 1 x ∈ reachableCylinderUnion X r (Fin.tail w) \
      shift 1 '' reachableCylinderUnion X r (Fin.tail w) := by
  subst hxw
  refine ⟨⟨hX 1 hx, ?_⟩, ?_⟩
  · simp only [word_shift, tail_word, add_zero, zero_add, Relation.ReflTransGen.refl]
  · rintro ⟨y, ⟨-, hy⟩, hyx⟩
    obtain rfl := shift_one_injective hyx
    refine not_reflTransGen_of_not_isCyclicEdge hw hnc ?_
    rwa [init_word]

/-- sec:chain-core: a noncyclic edge gives a cylinder union `P` with `P ∖ T(P)` nonempty. -/
theorem diff_image_shift_nonempty_of_not_isCyclicEdge {X : Set (ℤ → A)}
    (hX : ∀ n : ℤ, MapsTo (shift n) X X) {r : ℕ} {w : Fin (r + 1) → A}
    (hw : w ∈ language X (r + 1)) (hnc : ¬ IsCyclicEdge X r w) :
    (reachableCylinderUnion X r (Fin.tail w) \
      shift 1 '' reachableCylinderUnion X r (Fin.tail w)).Nonempty := by
  obtain ⟨x, hx, hxw⟩ := id hw
  exact ⟨shift 1 x, shift_mem_diff_of_not_isCyclicEdge hX hw hnc hx hxw⟩

#audit_axioms mapsTo_shift_reachableCylinderUnion
#audit_axioms shift_mem_diff_of_not_isCyclicEdge
#audit_axioms diff_image_shift_nonempty_of_not_isCyclicEdge
#audit_axioms isClosed_reachableCylinderUnion

end GroupApproximation.ChainCore
