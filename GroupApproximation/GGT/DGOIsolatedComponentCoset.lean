import GroupApproximation.GGT.DGOIsolatedComponentWitness
import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# A component stays in one coset, and why isolatedness is in the binder

The bridge to `IsolatedComponentBound` runs as follows: the complement of an
isolated component is a path from one end of the component to the other that
reads no `H lam`-letter inside the coset `(vertex v w i) · H lam`, so translating
it to the basepoint gives a `d̂_lam`-path and the span lands in a relative ball.
This module proves the coset half of that, and records the reason isolatedness
cannot be dropped.

## Vertices inside a component

`connected_of_mem_comp`: if `[i,k)` is an `H lam`-component of `w`, then every
vertex between `i` and `k` is `Connected` to `vertex v w i` --- the letters
crossed are `lam`-letters, and an admissible `lam`-letter has its value in
`H lam`, so the running product stays in one left coset.  That is what makes
`Connected` the right relation to state isolatedness with, and it is the step
the bridge uses to turn a `lam`-letter of the complement into a statement about
the component it belongs to.

## Why `IsIsolated` is a hypothesis and not a convenience

`connected_pair` and `not_avoidsFrom_complement_of_connected` are the two halves
of a configuration in which the bridge's conclusion fails.  Take

    w = [comp lam a, base x, base x⁻¹, comp lam a⁻¹] ,   a ∈ H lam ,

a closed path with `H lam`-components at `0` and at `3`.  They are `Connected`:
the vertex at `3` is `a`, which lies in `H lam`.  So by
`not_isolated_of_connected` neither component is isolated --- and the complement
of the one at `0`, namely `[base x, base x⁻¹, comp lam a⁻¹]` read from the
basepoint, reads its `lam`-letter at the vertex `1 · x · x⁻¹ = 1`, which lies in
`H lam`.  The complement is therefore not an admissible path, and no bound on
the span follows from it.

So `IsIsolated` is doing the work in the binder: it is exactly what excludes a
second component of the same coset, and without it the argument has no path to
run on.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  A component stays in one left coset -/

/-- **Every vertex of a component is connected to its start.**  Induction along
the component: each letter crossed is an admissible `lam`-letter, so it
multiplies the running product by an element of `H lam`. -/
theorem connected_of_mem_comp (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k) :
    ∀ j : ℕ, i ≤ j → j ≤ k → Connected D.fam lam v w i j := by
  obtain ⟨hik, hkw, hrun, -, -⟩ := hcomp
  intro j
  induction j with
  | zero =>
      intro hij _
      have hi0 : i = 0 := Nat.le_zero.mp hij
      subst hi0
      exact connected_refl _ _ _ _ _
  | succ m ih =>
      intro hij hjk
      rcases Nat.lt_or_ge m i with hlt | hge
      · have him : i = m + 1 := by omega
        subst him
        exact connected_refl _ _ _ _ _
      · have hmk : m < k := by omega
        have hmw : m < w.length := by omega
        have hprev : Connected D.fam lam v w i m := ih hge (by omega)
        have hval : (w[m]'hmw).val ∈ D.fam lam :=
          val_mem_fam_of_isCompOf D (hlet _ (List.getElem_mem hmw))
            (hrun m hge hmk hmw)
        have hstep : vertex v w (m + 1) = vertex v w m * (w[m]'hmw).val :=
          vertex_succ w v m hmw
        show (vertex v w i)⁻¹ * vertex v w (m + 1) ∈ D.fam lam
        rw [hstep, ← mul_assoc]
        exact mul_mem hprev hval

/-! ## 2.  The configuration that isolatedness excludes -/

/-- **Two components of one closed path, connected.**  The vertex at index `3`
of `[comp lam a, base x, base x⁻¹, comp lam a⁻¹]` is `a`, which lies in
`H lam`. -/
theorem connected_pair (D : RelGenSet G Λ) (lam : Λ) (x : G) {a : G}
    (ha : a ∈ D.fam lam) :
    Connected D.fam lam 1
      [RelLetter.comp lam a, RelLetter.base x, RelLetter.base x⁻¹,
        RelLetter.comp lam a⁻¹] 0 3 := by
  show ((1 : G))⁻¹ * ((1 : G) * a * x * x⁻¹) ∈ D.fam lam
  have hv : ((1 : G))⁻¹ * ((1 : G) * a * x * x⁻¹) = a := by group
  rw [hv]
  exact ha

/-- **The complement of a non-isolated component is not an admissible path.**
Read from the basepoint, `[base x, base x⁻¹, comp lam a⁻¹]` reads its
`lam`-letter at the vertex `1 · x · x⁻¹ = 1`, which lies in `H lam`.  This is
the complement of the component at `0` in `connected_pair`, so the bridge's
conclusion has no path to run on once isolatedness fails. -/
theorem not_avoidsFrom_complement_of_connected (D : RelGenSet G Λ) (lam : Λ)
    (x a : G) :
    ¬ AvoidsFrom D.fam lam
      [RelLetter.base x, RelLetter.base x⁻¹, RelLetter.comp lam a⁻¹] (1 : G) := by
  rintro ⟨-, -, h3, -⟩
  refine h3 ⟨rfl, ?_⟩
  show ((1 : G) * x * x⁻¹) ∈ D.fam lam
  rw [mul_inv_cancel_right]
  exact one_mem _

end OsinComponents
end GGT
end GroupApproximation
