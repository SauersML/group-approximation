import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.TripleLists
import GroupApproximation.Meta.AxiomGuard

/-!
# The three-dart lake cases of the region choice

Lane gl-p10-69.  Generic (any relation `s`, any nodup walk `c`, any `f`, in use `f = alpha`)
forms of the three lake cases in which a region meets the walk from outside in exactly THREE
darts `a1`, `a2`, `a3`, cyclically consecutive on `c`, the witness `y = a1` named explicitly:

* `roseLobeTriple_lake_run`: `c = A ++ [a1, a2, a3] ++ C`, `A ++ C ≠ []`: block
  `B = [a1, a2, a3]` removed;
* `roseLobeTriple_lake_wrapL`: `c = [a1] ++ M ++ [a2, a3]`, `M ≠ []`: block `B = M` kept, the
  first dart and the last two removed;
* `roseLobeTriple_lake_wrapR`: `c = [a1, a2] ++ M ++ [a3]`, `M ≠ []`: block `B = M` kept, the
  first two darts and the last removed.

In each, `f a1 ~ f a2`, `f a1 ~ f a3`, no other `e ∈ c` has `f e` in that class, and the class
misses `PO` and `PS`.  No contiguity hypothesis: the three darts are given with their positions.

## LOUD: strength

Everything here is PROVED; there is no hypothesis Prop.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section TripleLake

variable {α : Type*}

/-- **Consecutive lake triple.**  Three consecutive darts `a1`, `a2`, `a3` of `c` whose
`f`-images share a class that no other `f e` (`e ∈ c`) meets and that misses `PO`, `PS`: the
lake at `a1` with the removed block `B = [a1, a2, a3]`. -/
theorem roseLobeTriple_lake_run {s : α → α → Prop} {c A C : List α} {f : α → α}
    {PO PS : α → Prop} {a1 a2 a3 : α} (hnd : c.Nodup) (hc : c = A ++ [a1, a2, a3] ++ C)
    (hne : A ++ C ≠ []) (h12 : Relation.EqvGen s (f a1) (f a2))
    (h13 : Relation.EqvGen s (f a1) (f a3))
    (hlone : ∀ e ∈ c, Relation.EqvGen s (f a1) (f e) → e ∈ [a1, a2, a3])
    (hO : ∀ x, PO x → ¬Relation.EqvGen s (f a1) x)
    (hS : ∀ x, PS x → ¬Relation.EqvGen s (f a1) x) :
    ∃ y ∈ c, (∀ x, PO x → ¬Relation.EqvGen s (f y) x) ∧
      (∀ x, PS x → ¬Relation.EqvGen s (f y) x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun d => ¬Relation.EqvGen s (f y) (f d)) A B C := by
  have hB : ∀ d ∈ [a1, a2, a3], ¬¬Relation.EqvGen s (f a1) (f d) :=
    roseLobeTriple_forall_three (P := fun d => ¬¬Relation.EqvGen s (f a1) (f d))
      (fun h => h (Relation.EqvGen.refl (f a1))) (fun h => h h12) (fun h => h h13)
  have hQ : ∀ e ∈ A ++ C, ¬Relation.EqvGen s (f a1) (f e) := fun e he hre =>
    roseLobeTriple_not_mem_B hc hnd he (hlone e (roseLobeRegion_mem_AC hc he) hre)
  refine ⟨a1, roseLobeRegion_mem_B hc List.mem_cons_self, hO, hS, A, [a1, a2, a3], C, ?_⟩
  unfold roseLobeRegion_Block
  exact ⟨hc, Or.inl ⟨hB, hQ, hne⟩⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_lake_run

/-- **Lake triple wrapping after the first dart.**  The first dart `a1` and the last two darts
`a2`, `a3` of `c = [a1] ++ M ++ [a2, a3]`, with the `f`-class as in `roseLobeTriple_lake_run`
and a nonempty middle `M`: the lake at `a1` with the kept block `B = M`. -/
theorem roseLobeTriple_lake_wrapL {s : α → α → Prop} {c M : List α} {f : α → α}
    {PO PS : α → Prop} {a1 a2 a3 : α} (hnd : c.Nodup) (hc : c = [a1] ++ M ++ [a2, a3])
    (hM : M ≠ []) (h12 : Relation.EqvGen s (f a1) (f a2))
    (h13 : Relation.EqvGen s (f a1) (f a3))
    (hlone : ∀ e ∈ c, Relation.EqvGen s (f a1) (f e) → e ∈ [a1, a2, a3])
    (hO : ∀ x, PO x → ¬Relation.EqvGen s (f a1) x)
    (hS : ∀ x, PS x → ¬Relation.EqvGen s (f a1) x) :
    ∃ y ∈ c, (∀ x, PO x → ¬Relation.EqvGen s (f y) x) ∧
      (∀ x, PS x → ¬Relation.EqvGen s (f y) x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun d => ¬Relation.EqvGen s (f y) (f d)) A B C := by
  have hdef : [a1] ++ [a2, a3] = [a1, a2, a3] := rfl
  have hAC : ∀ d ∈ [a1] ++ [a2, a3], ¬¬Relation.EqvGen s (f a1) (f d) := by
    rw [hdef]
    exact roseLobeTriple_forall_three (P := fun d => ¬¬Relation.EqvGen s (f a1) (f d))
      (fun h => h (Relation.EqvGen.refl (f a1))) (fun h => h h12) (fun h => h h13)
  have hQ : ∀ e ∈ M, ¬Relation.EqvGen s (f a1) (f e) := by
    intro e he hre
    have h := hlone e (roseLobeRegion_mem_B hc he) hre
    rw [← hdef] at h
    exact roseLobeTriple_not_mem_B hc hnd h he
  refine ⟨a1, roseLobeRegion_mem_AC hc
    (List.mem_append_left [a2, a3] (List.mem_singleton_self a1)), hO, hS, [a1], M, [a2, a3], ?_⟩
  unfold roseLobeRegion_Block
  exact ⟨hc, Or.inr ⟨hQ, hAC, hM⟩⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_lake_wrapL

/-- **Lake triple wrapping after the second dart.**  The first two darts `a1`, `a2` and the last
dart `a3` of `c = [a1, a2] ++ M ++ [a3]`, with the `f`-class as in `roseLobeTriple_lake_run` and
a nonempty middle `M`: the lake at `a1` with the kept block `B = M`. -/
theorem roseLobeTriple_lake_wrapR {s : α → α → Prop} {c M : List α} {f : α → α}
    {PO PS : α → Prop} {a1 a2 a3 : α} (hnd : c.Nodup) (hc : c = [a1, a2] ++ M ++ [a3])
    (hM : M ≠ []) (h12 : Relation.EqvGen s (f a1) (f a2))
    (h13 : Relation.EqvGen s (f a1) (f a3))
    (hlone : ∀ e ∈ c, Relation.EqvGen s (f a1) (f e) → e ∈ [a1, a2, a3])
    (hO : ∀ x, PO x → ¬Relation.EqvGen s (f a1) x)
    (hS : ∀ x, PS x → ¬Relation.EqvGen s (f a1) x) :
    ∃ y ∈ c, (∀ x, PO x → ¬Relation.EqvGen s (f y) x) ∧
      (∀ x, PS x → ¬Relation.EqvGen s (f y) x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun d => ¬Relation.EqvGen s (f y) (f d)) A B C := by
  have hdef : [a1, a2] ++ [a3] = [a1, a2, a3] := rfl
  have hAC : ∀ d ∈ [a1, a2] ++ [a3], ¬¬Relation.EqvGen s (f a1) (f d) := by
    rw [hdef]
    exact roseLobeTriple_forall_three (P := fun d => ¬¬Relation.EqvGen s (f a1) (f d))
      (fun h => h (Relation.EqvGen.refl (f a1))) (fun h => h h12) (fun h => h h13)
  have hQ : ∀ e ∈ M, ¬Relation.EqvGen s (f a1) (f e) := by
    intro e he hre
    have h := hlone e (roseLobeRegion_mem_B hc he) hre
    rw [← hdef] at h
    exact roseLobeTriple_not_mem_B hc hnd h he
  refine ⟨a1, roseLobeRegion_mem_AC hc
    (List.mem_append_left [a3] List.mem_cons_self), hO, hS, [a1, a2], M, [a3], ?_⟩
  unfold roseLobeRegion_Block
  exact ⟨hc, Or.inr ⟨hQ, hAC, hM⟩⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_lake_wrapR

end TripleLake

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
