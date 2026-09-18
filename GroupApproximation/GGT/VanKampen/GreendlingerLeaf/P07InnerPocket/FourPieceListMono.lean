import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: monochrome side chunks

Lane `gl-p07-10` (`lanes/carto-gl-p07.md`), list layer.  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`; certifies no printed sentence on its own.
The mathematical proof of the lane is in `FourPieceOrder.lean`.

## Statement

`mono_or`: if every entry of `X` is `Pa` or `Pb`, and no ordered pair of entries of `X` consists
of a non-`Pb` entry and a `Pb` entry (in either order), then `X` is all `Pa` or all `Pb`.

## Proof

If some `x₁ ∈ X` is not `Pb`, then any `x₂ ∈ X` that is not `Pa` is `Pb`, so `x₂ ≠ x₁`; it lies
before or after `x₁`, and `[x₂, x₁]` or `[x₁, x₂]` is a sublist of `X`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece

section Lists

variable {α : Type*}

/-- An entry of a rotation is an entry of the list. -/
theorem mem_of_rotate_eq {l l' : List α} {n : ℕ} (hn : l.rotate n = l') {x : α} (hx : x ∈ l') :
    x ∈ l := by
  rw [← hn] at hx
  exact List.mem_rotate.mp hx

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.mem_of_rotate_eq

/-- Four entries of four blocks, skipping a block after the first, form a sublist. -/
theorem sublist_four_skip {x y z t : α} {l₁ l₀ l₂ l₃ l₄ : List α} (h₁ : x ∈ l₁) (h₂ : y ∈ l₂)
    (h₃ : z ∈ l₃) (h₄ : t ∈ l₄) : [x, y, z, t] <+ l₁ ++ (l₀ ++ (l₂ ++ (l₃ ++ l₄))) :=
  (List.singleton_sublist.mpr h₁).append (((List.singleton_sublist.mpr h₂).append
    ((List.singleton_sublist.mpr h₃).append (List.singleton_sublist.mpr h₄))).trans
      (List.sublist_append_right l₀ _))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.sublist_four_skip

/-- **Monochrome chunk.**  A chunk of `Pa`-or-`Pb` entries with no pair of a non-`Pb` entry and a
`Pb` entry, in either order, is all `Pa` or all `Pb`. -/
theorem mono_or {Pa Pb : α → Prop} {X : List α} (hs : ∀ x ∈ X, Pa x ∨ Pb x)
    (hab : ∀ x₁ x₂, [x₁, x₂] <+ X → ¬ Pb x₁ → Pb x₂ → False)
    (hba : ∀ x₁ x₂, [x₂, x₁] <+ X → ¬ Pb x₁ → Pb x₂ → False) :
    (∀ x ∈ X, Pa x) ∨ ∀ x ∈ X, Pb x := by
  by_cases hb : ∀ x ∈ X, Pb x
  · exact Or.inr hb
  · left
    obtain ⟨x₁, hx₁, hnb⟩ : ∃ x ∈ X, ¬ Pb x :=
      Classical.byContradiction fun hc => hb fun x hx =>
        Classical.byContradiction fun hx' => hc ⟨x, hx, hx'⟩
    intro x₂ hx₂
    refine Classical.byContradiction fun hna => ?_
    have hb₂ : Pb x₂ := (hs x₂ hx₂).resolve_left hna
    obtain ⟨X₁, X₂, hX⟩ := List.append_of_mem hx₁
    rw [hX] at hx₂ hab hba
    rcases List.mem_append.mp hx₂ with h₂ | h₂
    · have hp : [x₂, x₁] <+ X₁ ++ x₁ :: X₂ :=
        (List.singleton_sublist.mpr h₂).append (List.singleton_sublist.mpr List.mem_cons_self)
      exact hba x₁ x₂ hp hnb hb₂
    · rcases List.mem_cons.mp h₂ with h₂ | h₂
      · exact hnb (by rw [← h₂]; exact hb₂)
      · have hp : [x₁, x₂] <+ X₁ ++ x₁ :: X₂ :=
          (List.nil_sublist X₁).append ((List.singleton_sublist.mpr h₂).cons_cons x₁)
        exact hab x₁ x₂ hp hnb hb₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.mono_or

end Lists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece
