import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.MultiLists
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-dart lake cases of the region choice

Lane gl-p10-67.  Generic (any relation `s`, any nodup walk `c`, any `f`, in use `f = alpha`)
forms of the two lake cases in which a region meets the walk from outside in exactly TWO darts,
cyclically adjacent on `c`:

* `roseLobeMulti_lake_pair`: `c = A ++ [a, b] ++ C`, `f a ~ f b`, no other `e ∈ c` has `f e` in
  that class, the class misses `PO`, `PS`, and `A ++ C ≠ []`: the lake at `a`, block `B = [a, b]`
  removed;
* `roseLobeMulti_lake_wrap`: the same with `c = [a] ++ M ++ [b]`, `M ≠ []`: the lake at `a`,
  block `B = M` kept, the two ends removed.

In the random truth check (see `MultiStatement`; seeds 0-7, `N = 60`, `maxeps 2`) the lake pair
applies to `4234` and the lake wrap to `1240` of the `5634` residual configurations of
`roseLobeChoice_Statement` (the cases overlap).

## LOUD: strength

Everything here is PROVED; there is no hypothesis Prop.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section MultiLake

variable {α : Type*}

/-- **Adjacent lake pair.**  Two consecutive darts `a`, `b` of `c` whose `f`-images share a
class that no other `f e` (`e ∈ c`) meets and that misses `PO`, `PS`: the lake at `a` with the
removed block `B = [a, b]`. -/
theorem roseLobeMulti_lake_pair {s : α → α → Prop} {c A C : List α} {f : α → α}
    {PO PS : α → Prop} {a b : α} (hnd : c.Nodup) (hc : c = A ++ [a, b] ++ C)
    (hne : A ++ C ≠ []) (hab : Relation.EqvGen s (f a) (f b))
    (hlone : ∀ e ∈ c, Relation.EqvGen s (f a) (f e) → e = a ∨ e = b)
    (hO : ∀ x, PO x → ¬Relation.EqvGen s (f a) x)
    (hS : ∀ x, PS x → ¬Relation.EqvGen s (f a) x) :
    ∃ y ∈ c, (∀ x, PO x → ¬Relation.EqvGen s (f y) x) ∧
      (∀ x, PS x → ¬Relation.EqvGen s (f y) x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun d => ¬Relation.EqvGen s (f y) (f d)) A B C := by
  have hQa : ¬¬Relation.EqvGen s (f a) (f a) := fun h => h (Relation.EqvGen.refl (f a))
  have hQb : ¬¬Relation.EqvGen s (f a) (f b) := fun h => h hab
  have hQ : ∀ e ∈ A ++ C, ¬Relation.EqvGen s (f a) (f e) := by
    intro e he hre
    have hea := roseLobeMulti_ne_of_mem_pair hc hnd he
    rcases hlone e (roseLobeMulti_mem_of_mem_AC_pair hc he) hre with h | h
    · exact hea.1 h
    · exact hea.2 h
  exact ⟨a, roseLobeMulti_mem_left_pair hc, hO, hS, A, [a, b], C,
    roseLobeMulti_block_pair (Q := fun d => ¬Relation.EqvGen s (f a) (f d)) hc hne hQa hQb hQ⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_lake_pair

/-- **Lake pair at the ends.**  The first dart `a` and the last dart `b` of `c`, with the
`f`-class as in `roseLobeMulti_lake_pair` and a nonempty middle `M`: the lake at `a` with the
kept block `B = M`. -/
theorem roseLobeMulti_lake_wrap {s : α → α → Prop} {c M : List α} {f : α → α}
    {PO PS : α → Prop} {a b : α} (hnd : c.Nodup) (hc : c = [a] ++ M ++ [b])
    (hM : M ≠ []) (hab : Relation.EqvGen s (f a) (f b))
    (hlone : ∀ e ∈ c, Relation.EqvGen s (f a) (f e) → e = a ∨ e = b)
    (hO : ∀ x, PO x → ¬Relation.EqvGen s (f a) x)
    (hS : ∀ x, PS x → ¬Relation.EqvGen s (f a) x) :
    ∃ y ∈ c, (∀ x, PO x → ¬Relation.EqvGen s (f y) x) ∧
      (∀ x, PS x → ¬Relation.EqvGen s (f y) x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun d => ¬Relation.EqvGen s (f y) (f d)) A B C := by
  have hQa : ¬¬Relation.EqvGen s (f a) (f a) := fun h => h (Relation.EqvGen.refl (f a))
  have hQb : ¬¬Relation.EqvGen s (f a) (f b) := fun h => h hab
  have hQ : ∀ e ∈ M, ¬Relation.EqvGen s (f a) (f e) := by
    intro e he hre
    have hea := roseLobeMulti_ne_of_mem_wrap hc hnd he
    rcases hlone e (roseLobeMulti_mem_of_mem_wrap hc he) hre with h | h
    · exact hea.1 h
    · exact hea.2 h
  exact ⟨a, roseLobeMulti_mem_left_wrap hc, hO, hS, [a], M, [b],
    roseLobeMulti_block_wrap (Q := fun d => ¬Relation.EqvGen s (f a) (f d)) hc hM hQa hQb hQ⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_lake_wrap

end MultiLake

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
