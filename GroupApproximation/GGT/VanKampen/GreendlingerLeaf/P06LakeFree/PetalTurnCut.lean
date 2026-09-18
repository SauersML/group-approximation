import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurnConvex
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalInvWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: the search invariant and its helpers (lane gl-p06-18)

Infrastructure for `P06LakeFree.PetalTurn.cellPocketLakeFreePetalTurn`
(`P06LakeFree/PetalTurnClose.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Truth check

`PetalTurnEnv X T t₁ t₂` records what the pocket boundary `T = ∂K` and the two reversed arcs
`t₁`, `t₂` provide: `T` has no repeats and no bridge, the `tᵢ` are infixes of `T`, and consecutive
darts `d, e` of `tᵢ` satisfy `σ e = α d` (the reverse of a face boundary turns by `σ`).
`PetalTurnInv X T t₁ t₂ x₀ W₀` says that `W₀` is a closed vertex walk whose reverse is a sublist of
`T`, convex in both `tᵢ`, with the face of `x₀` on its side.  The initial walk is `∂K` reversed.

## The mathematical proof

1. `invDarts` reverses concatenations; its first and last darts are `α` of the last and first
   darts (`invDarts_append`, `head?_invDarts`, `getLast?_invDarts`).
2. *Adjacent reversed arc darts turn* (`sigma_eq_of_adjacent`): `t = p ++ a :: b :: q` gives
   `σ b = α a` by the chain of `t`.
3. *Translation of a bad junction* (`not_adjacent_of_bad`).  For `W₀ = u ++ y :: B ++ y' :: v`,
   `invDarts W₀ = invDarts (y' :: v) ++ invDarts (y :: B) ++ invDarts u`.  An adjacency on `t` at
   the first junction reads `σ (α x) = α (α y') = y'` for the last dart `x` of `y :: B`; at the
   second, `σ (α x) = y` for the last dart `x` of `u`.
4. *Sides split* (`side_split`).  A side face of `invDarts W₀` is reached from some dart `d` with
   `α d ∈ W₀`; `α d` lies on one piece, and the face class moves to the smaller keep set
   (`faceClass_mono`, `petal_walkKeep_invDarts`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn

open Embedded SimpleClosedWalkSides

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The environment of the petal search**: a boundary without repeats or bridges and two
turning infixes. -/
structure PetalTurnEnv (X : DiscDiagram.{u, w, v} W) (T t₁ t₂ : List X.toCombMap.Dart) :
    Prop where
  nodup : T.Nodup
  infix₁ : t₁ <:+: T
  infix₂ : t₂ <:+: T
  chain₁ : t₁.IsChain fun d e => X.toCombMap.sigma e = X.toCombMap.alpha d
  chain₂ : t₂.IsChain fun d e => X.toCombMap.sigma e = X.toCombMap.alpha d
  no_bridge : ∀ d ∈ T, X.toCombMap.alpha d ∉ T

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.PetalTurnEnv

/-- **The invariant of the petal search.** -/
structure PetalTurnInv (X : DiscDiagram.{u, w, v} W) (T t₁ t₂ : List X.toCombMap.Dart)
    (x₀ : X.toCombMap.Dart) (W₀ : List X.toCombMap.Dart) : Prop where
  ne_nil : W₀ ≠ []
  chain : W₀.IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e
  closes : ∀ a ∈ W₀.getLast?, ∀ b ∈ W₀.head?,
    X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b
  sublist : invDarts X W₀ <+ T
  conv₁ : OrderCactus.RunConvex (invDarts X W₀) t₁
  conv₂ : OrderCactus.RunConvex (invDarts X W₀) t₂
  side : X.toCombMap.faceOf x₀ ∈ sideFaces X.toCombMap (invDarts X W₀)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.PetalTurnInv

/-- The inverse walk reverses concatenations. -/
theorem invDarts_append (X : DiscDiagram.{u, w, v} W) (l₁ l₂ : List X.toCombMap.Dart) :
    invDarts X (l₁ ++ l₂) = invDarts X l₂ ++ invDarts X l₁ := by
  simp only [invDarts, List.reverse_append, List.map_append]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.invDarts_append

/-- The last dart of the inverse walk. -/
theorem getLast?_invDarts (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart) :
    (invDarts X l).getLast? = l.head?.map X.toCombMap.alpha := by
  simp only [invDarts, List.getLast?_map, List.getLast?_reverse]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.getLast?_invDarts

/-- The first dart of the inverse walk. -/
theorem head?_invDarts (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart) :
    (invDarts X l).head? = l.getLast?.map X.toCombMap.alpha := by
  simp only [invDarts, List.head?_map, List.head?_reverse]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.head?_invDarts

/-- The last entry of a list ending in a nonempty piece. -/
theorem getLast?_append_cons {α : Type*} (l l' : List α) (a : α) :
    (l ++ a :: l').getLast? = (a :: l').getLast? := by
  rw [List.getLast?_append, List.getLast?_cons, Option.some_or]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.getLast?_append_cons

/-- Adjacent darts of a turning list turn. -/
theorem sigma_eq_of_adjacent {X : DiscDiagram.{u, w, v} W} {t p q : List X.toCombMap.Dart}
    {a b : X.toCombMap.Dart}
    (hchain : t.IsChain fun d e => X.toCombMap.sigma e = X.toCombMap.alpha d)
    (h : t = p ++ a :: b :: q) : X.toCombMap.sigma b = X.toCombMap.alpha a := by
  rw [h] at hchain
  exact (List.isChain_append_cons_cons.mp hchain).2.1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.sigma_eq_of_adjacent

/-- **Translation of a bad junction.**  If the walk `u ++ y :: B ++ y' :: v` does not turn at both
junctions, the reversed pieces are not adjacent on a turning list at both junctions. -/
theorem not_adjacent_of_bad {X : DiscDiagram.{u, w, v} W} {t u B v : List X.toCombMap.Dart}
    {y y' : X.toCombMap.Dart}
    (hchain : t.IsChain fun d e => X.toCombMap.sigma e = X.toCombMap.alpha d)
    (hbad : ¬ ((∃ x ∈ u.getLast?, X.toCombMap.sigma (X.toCombMap.alpha x) = y) ∧
      (∃ x ∈ (y :: B).getLast?, X.toCombMap.sigma (X.toCombMap.alpha x) = y'))) :
    ¬ ((∃ x ∈ (invDarts X (y' :: v)).getLast?, ∃ z ∈ (invDarts X (y :: B)).head?,
        ∃ p q, t = p ++ x :: z :: q) ∧
      (∃ x ∈ (invDarts X (y :: B)).getLast?, ∃ z ∈ (invDarts X u).head?,
        ∃ p q, t = p ++ x :: z :: q)) := by
  rintro ⟨⟨x, hx, z, hz, p, q, hpq⟩, ⟨x', hx', z', hz', p', q', hpq'⟩⟩
  refine hbad ⟨?_, ?_⟩
  · rw [Option.mem_def, head?_invDarts, Option.map_eq_some_iff] at hz'
    obtain ⟨z₀, hz₀, rfl⟩ := hz'
    rw [Option.mem_def, getLast?_invDarts, List.head?_cons, Option.map_some] at hx'
    have h := sigma_eq_of_adjacent hchain hpq'
    rw [← Option.some.inj hx', X.toCombMap.alpha_involutive] at h
    exact ⟨z₀, Option.mem_def.mpr hz₀, h⟩
  · rw [Option.mem_def, head?_invDarts, Option.map_eq_some_iff] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    rw [Option.mem_def, getLast?_invDarts, List.head?_cons, Option.map_some] at hx
    have h := sigma_eq_of_adjacent hchain hpq
    rw [← Option.some.inj hx, X.toCombMap.alpha_involutive] at h
    exact ⟨z₀, Option.mem_def.mpr hz₀, h⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.not_adjacent_of_bad

/-- **Sides split.**  A side face of a walk covered by two subwalks is a side face of one of
them. -/
theorem side_split {X : DiscDiagram.{u, w, v} W} {x₀ : X.toCombMap.Dart}
    {W₀ P₁ P₂ : List X.toCombMap.Dart} (h₁ : ∀ d ∈ P₁, d ∈ W₀) (h₂ : ∀ d ∈ P₂, d ∈ W₀)
    (hW : ∀ d ∈ W₀, d ∈ P₁ ∨ d ∈ P₂)
    (hs : X.toCombMap.faceOf x₀ ∈ sideFaces X.toCombMap (invDarts X W₀)) :
    X.toCombMap.faceOf x₀ ∈ sideFaces X.toCombMap (invDarts X P₁) ∨
      X.toCombMap.faceOf x₀ ∈ sideFaces X.toCombMap (invDarts X P₂) := by
  rw [mem_sideFaces_iff, Petal.petal_walkKeep_invDarts] at hs
  obtain ⟨d, hd, hg⟩ := hs
  rw [mem_sideFaces_iff, mem_sideFaces_iff, Petal.petal_walkKeep_invDarts,
    Petal.petal_walkKeep_invDarts]
  rcases hW _ ((Petal.petal_mem_invDarts_iff X).mp hd) with h | h
  · refine Or.inl ⟨d, (Petal.petal_mem_invDarts_iff X).mpr h, ?_⟩
    exact faceClass_mono X.toCombMap
      (fun x hx hx' => hx (hx'.imp (h₁ x) (h₁ (X.toCombMap.alpha x)))) hg
  · refine Or.inr ⟨d, (Petal.petal_mem_invDarts_iff X).mpr h, ?_⟩
    exact faceClass_mono X.toCombMap
      (fun x hx hx' => hx (hx'.imp (h₂ x) (h₂ (X.toCombMap.alpha x)))) hg

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.side_split

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn
