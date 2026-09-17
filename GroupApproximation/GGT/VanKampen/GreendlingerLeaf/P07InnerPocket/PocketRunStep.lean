import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Runs follow their piece: one step of the outer walk (lane `gl-p07-09`)

## Truth check: the lane statement as written is FALSE-AS-STATED (not derivable)

The lane asks: under `Hyp`, two cyclically consecutive darts `d = ow[p]`, `d' = ow[p+1]` of lane
06's outer walk that both lie on `G₁.darts` satisfy `facePerm d = d'`.  The step is not a
consequence of `EnclosedFaceSetSucc`, of `nodup`, or (as far as we can see) of `Hyp`.
`turn_next` only says `d' = σ^m (α d)` for the *first* `m > 0` whose dart is on a walk edge.
`facePerm d = σ (α d)` is the case `m = 1`, and it is forced only when `σ (α d)` is on a walk edge.
Inside `G₁` this holds (the next arc dart is a walk dart), but at the last dart of `G₁` it can fail.
**Model (pinched cell).**  Take `Π_i` with a boundary that touches itself at a vertex `v`.  Take
both contacts empty and `G₁ = firstArc` one lobe from `v` back to `v`, with the pocket, `a`, `b`
and `Π_j` across that lobe and the outer face across the other lobe.  At `d = G₁.last` the dart
`facePerm d` starts the other lobe, which is on no walk edge.  Turning from `α d`, the first walk
dart is `G₁[0]`, so `d' = G₁[0] ≠ facePerm d`.  Variants give runs `G₁[s..] ++ G₁[..t]` that are
no sub-arc of `cellDarts X i`.  The Euler hypotheses `hinner`/`houter` count one reclosing vertex
per walk dart, so they do not exclude such a pinch.

## What is proved instead (true, Hyp-free, over any `EnclosedFaceSetSucc`)

* `succ_eq_facePerm_of_keep`: if `facePerm ow[i]` is on a walk edge, it is `ow[i+1]`.
  (`turn_next` with `m = 1`, the minimality clause being vacuous.)
* `vertexOf_succ`: `ow[i+1]` starts where `facePerm ow[i]` starts.  (First return `m` from
  `Nat.find`, bounded by `orderOf σ`; `σ`-powers keep the vertex.)
* `succ_eq_facePerm_of_pinchFree`: if the face of `ow[i]` has no dart other than `facePerm ow[i]`
  starting at that vertex (`PinchFreeAt`), and `ow[i+1]` is on that face, then
  `ow[i+1] = facePerm ow[i]`.
* `PocketRunArc`: a duplicate-free `facePerm` chain of cell darts is the dart list of a
  `CyclicArc (cellDarts X k)`.  Among the darts of an arc, only the last one can have its
  `facePerm` off the arc.
* `PocketRunSplit`: for an arc `A` whose darts are walk darts, every block `u` of a rotation of
  the walk that lies on `A` is the concatenation of **at most two** sub-arcs, unconditionally.  It is
  **one** sub-arc when `PinchFreeAt` holds at the (unique) dart of `u` whose `facePerm` leaves `A`.
* `PocketRunStatement`: the corrected `PocketRunInfixStatement` and its proof `pocketRunInfix`.

The proof of the two-piece form: a junction `t` of `u` is an index where `facePerm u[t] ∉ A.darts`.
At every other index, `facePerm u[t]` is an arc dart and hence a walk dart, so the step lemma gives
`facePerm u[t] = u[t+1]`.  A junction dart is the last arc dart, and `u` has no repeated dart, so
there is at most one junction.  Split `u` after it; both halves are `facePerm` chains.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7 (the inner pocket); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open Embedded SimpleClosedWalkSides

universe u w v

namespace PocketRun

/-- Equal indices give equal entries, whatever the bound proofs. -/
theorem getElem_idx_congr {α : Type*} (l : List α) {i j : ℕ} (hij : i = j) (hi : i < l.length)
    (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst hij
  rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.getElem_idx_congr

section Map

variable {M : CombMap.{v}}

/-- Vertex rotations keep the vertex. -/
theorem vertexOf_sigma_pow (m : ℕ) (d : M.Dart) :
    M.vertexOf ((M.sigma ^ m) d) = M.vertexOf d := by
  induction m with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply, M.vertexOf_sigma, ih]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.vertexOf_sigma_pow

/-- The face successor is the vertex rotation of the reverse. -/
theorem facePerm_eq_sigma_alpha (d : M.Dart) : M.facePerm d = M.sigma (M.alpha d) := by
  rw [CombMap.facePerm, Equiv.Perm.mul_apply]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.facePerm_eq_sigma_alpha

/-- **The first kept dart after the reverse of a walk dart.** -/
theorem exists_firstKeep (w : List M.Dart) {d : M.Dart} (hd : d ∈ w) :
    ∃ m, 0 < m ∧ walkKeep M w ((M.sigma ^ m) (M.alpha d)) ∧
      ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) (M.alpha d)) := by
  classical
  have hex : ∃ m, 0 < m ∧ walkKeep M w ((M.sigma ^ m) (M.alpha d)) := by
    refine ⟨orderOf M.sigma, orderOf_pos _, ?_⟩
    rw [pow_orderOf_eq_one, Equiv.Perm.one_apply]
    exact Or.inr (by rw [M.alpha_involutive]; exact hd)
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun k hk hkm hkeep => Nat.find_min hex hkm ⟨hk, hkeep⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.exists_firstKeep

/-- **No pinch after `d`.**  The only dart of the face of `d` that starts at the end vertex of `d`
is `facePerm d`. -/
def PinchFreeAt (M : CombMap.{v}) (d : M.Dart) : Prop :=
  ∀ e : M.Dart, M.faceOf e = M.faceOf d → M.vertexOf e = M.vertexOf (M.facePerm d) →
    e = M.facePerm d

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.PinchFreeAt

end Map

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}

/-- **A kept face successor is the next walk dart.** -/
theorem succ_eq_facePerm_of_keep (E : EnclosedFaceSetSucc X F ow) (i : ℕ) (hi : i < ow.length)
    (hkeep : walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[i])) :
    X.toCombMap.facePerm ow[i] =
      ow[(i + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  rw [facePerm_eq_sigma_alpha] at hkeep ⊢
  have h1 := E.turn_next i hi 1 Nat.one_pos (by rw [pow_one]; exact hkeep)
    (fun k hk hk1 => absurd hk1 (by omega))
  rw [pow_one] at h1
  exact h1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.succ_eq_facePerm_of_keep

/-- **The next walk dart starts where the face successor starts.** -/
theorem vertexOf_succ (E : EnclosedFaceSetSucc X F ow) (i : ℕ) (hi : i < ow.length) :
    X.toCombMap.vertexOf
        (ow[(i + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) =
      X.toCombMap.vertexOf (X.toCombMap.facePerm ow[i]) := by
  obtain ⟨m, hm, hkeep, hfirst⟩ := exists_firstKeep ow (List.getElem_mem hi)
  have h := E.turn_next i hi m hm hkeep hfirst
  have hv : X.toCombMap.vertexOf ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha ow[i])) =
      X.toCombMap.vertexOf (X.toCombMap.facePerm ow[i]) := by
    rw [vertexOf_sigma_pow, facePerm_eq_sigma_alpha, X.toCombMap.vertexOf_sigma]
  rw [h] at hv
  exact hv

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.vertexOf_succ

/-- **Without a pinch, a next walk dart on the same face is the face successor.** -/
theorem succ_eq_facePerm_of_pinchFree (E : EnclosedFaceSetSucc X F ow) (i : ℕ)
    (hi : i < ow.length) (hpinch : PinchFreeAt X.toCombMap ow[i])
    (hface : X.toCombMap.faceOf
        (ow[(i + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) =
      X.toCombMap.faceOf ow[i]) :
    X.toCombMap.facePerm ow[i] =
      ow[(i + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) :=
  (hpinch _ hface (vertexOf_succ E i hi)).symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.succ_eq_facePerm_of_pinchFree

/-- **One step inside the walk**, at a non-final index. -/
theorem succ_eq_facePerm (E : EnclosedFaceSetSucc X F ow) (i : ℕ) (hi : i + 1 < ow.length)
    (h : walkKeep X.toCombMap ow (X.toCombMap.facePerm (ow[i]'(by omega))) ∨
      (PinchFreeAt X.toCombMap (ow[i]'(by omega)) ∧
        X.toCombMap.faceOf ow[i + 1] = X.toCombMap.faceOf (ow[i]'(by omega)))) :
    X.toCombMap.facePerm (ow[i]'(by omega)) = ow[i + 1] := by
  have hi' : i < ow.length := by omega
  have hidx : ow[(i + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi')) =
      ow[i + 1] := getElem_idx_congr ow (Nat.mod_eq_of_lt hi) _ hi
  rcases h with hkeep | ⟨hpinch, hface⟩
  · exact (succ_eq_facePerm_of_keep E i hi' hkeep).trans hidx
  · exact (succ_eq_facePerm_of_pinchFree E i hi' hpinch (by rw [hidx]; exact hface)).trans hidx

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.succ_eq_facePerm

end PocketRun

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
