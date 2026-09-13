import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionUnpinched
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryEnumeration
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Boundary circuits of a face set are noncrossing closed walks

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

A boundary walk of a face set from `d` rotates around one vertex from `alpha d`, through internal
darts only, to the next boundary dart.  An internal dart lies on no edge of a list of boundary
darts.  So a list of boundary darts in which each dart is joined to the next, and the last to the
first, by a boundary walk is a noncrossing closed walk: rotating from `alpha d`, the first dart met
on an edge of the list is the next dart of the list.  No planarity is used, and the face set may
have several boundary circuits.  Such a list is the boundary circuit through any of its darts.

* `Surgery.MapCollapse.BoundaryWalk.mono`: a boundary walk of a face set is one of every larger
  face set.
* `Surgery.MapCollapse.BoundaryWalk.trans_internal`: a walk that reaches an internal dart crosses
  its edge and continues from the reversal.
* `Embedded.boundaryWalk_of_boundaryStep`: a boundary step of a diagram face set is a boundary
  walk.
* `Surgery.MapCollapse.BoundaryWalk.exists_pow`: a boundary walk rotates from `alpha d` through
  internal darts.
* `Surgery.MapCollapse.FaceSetCircuits.boundaryPerm_val_of_boundaryWalk`: a boundary walk between
  boundary darts is the step of the boundary permutation.
* `Surgery.MapCollapse.isNoncrossingClosedWalk_of_isChain_boundaryWalk`: a chained list of boundary
  darts is a noncrossing closed walk.
* `Surgery.MapCollapse.FaceSetCircuits.circuit_isNoncrossingClosedWalk`: every boundary circuit of
  every face set is a noncrossing closed walk.
* `Surgery.MapCollapse.FaceSetCircuits.mem_circuit_iff_of_isChain_boundaryWalk`: a chained list of
  boundary darts is the circuit through any of its darts.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv SimpleClosedWalkSides NoncrossingClosedWalkSides

universe u w v

namespace Surgery.MapCollapse

variable {M : CombMap.{v}} {faces faces' : Finset M.Face}

/-- **A boundary walk of a smaller face set.**  An internal dart of a face set is internal to every
larger face set. -/
theorem BoundaryWalk.mono (hsub : faces ⊆ faces') {d e : M.Dart}
    (h : BoundaryWalk M faces d e) : BoundaryWalk M faces' d e := by
  unfold BoundaryWalk at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih => exact ih.tail ⟨⟨hsub hxy.1.1, hsub hxy.1.2⟩, hxy.2⟩

/-- **A walk through an internal dart.**  A boundary walk that reaches an internal dart `u`
crosses its edge and continues as a boundary walk from `alpha u`. -/
theorem BoundaryWalk.trans_internal {d u e : M.Dart} (h₁ : BoundaryWalk M faces d u)
    (hu : InternalDart M faces u) (h₂ : BoundaryWalk M faces (M.alpha u) e) :
    BoundaryWalk M faces d e := by
  unfold BoundaryWalk at h₁ h₂ ⊢
  have hface : M.facePerm (M.alpha u) = M.sigma u := congrArg M.sigma (M.alpha_involutive u)
  rw [hface] at h₂
  exact (h₁.tail ⟨hu, rfl⟩).trans h₂

/-- **A boundary walk rotates around one vertex.**  A boundary walk from `d` to `e` reaches `e`
after `n + 1` rotation steps from `alpha d`, and every dart strictly between is internal. -/
theorem BoundaryWalk.exists_pow {d e : M.Dart} (h : BoundaryWalk M faces d e) :
    ∃ n : ℕ, (M.sigma ^ (n + 1)) (M.alpha d) = e ∧
      ∀ k, 0 < k → k ≤ n → InternalDart M faces ((M.sigma ^ k) (M.alpha d)) := by
  have h' : Relation.ReflTransGen (fun x y => InternalDart M faces x ∧ M.sigma x = y)
      (M.facePerm d) e := h
  obtain ⟨n, hn, hskip⟩ :=
    PermFirstReturn.exists_pow_of_skip_walk M.sigma (InternalDart M faces) h'
  have hface : M.facePerm d = M.sigma (M.alpha d) := rfl
  refine ⟨n, ?_, fun k hk hkn => ?_⟩
  · rw [pow_succ, Perm.mul_apply, ← hface]
    exact hn
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, Perm.mul_apply, ← hface]
    exact hskip j (by omega)

/-- In a list chained by `R` and closed by `R` from its last to its first element, every element
has a successor in the list. -/
private theorem exists_mem_rel_of_isChain {α : Type*} {R : α → α → Prop} {l : List α}
    (hne : l ≠ []) (hchain : l.IsChain R) (hclose : R (l.getLast hne) (l.head hne))
    {a : α} (ha : a ∈ l) : ∃ b ∈ l, R a b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  by_cases hlast : i + 1 < l.length
  · exact ⟨l[i + 1], List.getElem_mem hlast, List.isChain_iff_getElem.mp hchain i (by omega)⟩
  · refine ⟨l.head hne, List.head_mem hne, ?_⟩
    have hgl : l[i] = l.getLast hne := by
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    rw [hgl]
    exact hclose

/-- **A chained list of boundary darts is a noncrossing closed walk.**  Let `w` be a list of
distinct boundary darts of a face set in which each dart is joined to the next, and the last to
the first, by a boundary walk.  Rotating from `alpha d` for a dart `d` of `w`, the walk to the next
dart passes only internal darts, and an internal dart lies on no edge of `w`.  So the first dart
met on an edge of `w` is the next dart of `w`. -/
theorem isNoncrossingClosedWalk_of_isChain_boundaryWalk {w : List M.Dart} (hne : w ≠ [])
    (hnodup : w.Nodup) (hbd : ∀ d ∈ w, IsBoundaryDart M faces d)
    (hchain : w.IsChain (BoundaryWalk M faces))
    (hclose : BoundaryWalk M faces (w.getLast hne) (w.head hne)) :
    IsNoncrossingClosedWalk M w where
  ne_nil := hne
  nodup := hnodup
  chain := hchain.imp fun _ _ h => (vertexOf_eq_of_boundaryWalk h).symm
  closes := (vertexOf_eq_of_boundaryWalk hclose).symm
  alpha_not_mem d hd := fun had => (hbd d hd).2 (hbd _ had).1
  turn_mem d hd := by
    obtain ⟨e, he, hwalk⟩ := exists_mem_rel_of_isChain hne hchain hclose hd
    obtain ⟨n, hn, hint⟩ := hwalk.exists_pow
    refine turn_mem_of_first (m₀ := n + 1) (Nat.succ_pos n) ?_ ?_
    · rw [hn]
      exact he
    · intro k hk hkn hkeep
      have hi := hint k hk (by omega)
      have hkeep' : (M.sigma ^ k) (M.alpha d) ∈ w ∨ M.alpha ((M.sigma ^ k) (M.alpha d)) ∈ w :=
        hkeep
      rcases hkeep' with hmem | hrev
      · exact (hbd _ hmem).2 hi.2
      · have hb := (hbd _ hrev).2
        rw [M.alpha_involutive ((M.sigma ^ k) (M.alpha d))] at hb
        exact hb hi.1

namespace FaceSetCircuits

/-- **A boundary walk is the actual successor.**  A boundary walk from a boundary dart to a
boundary dart is the step of the boundary permutation. -/
theorem boundaryPerm_val_of_boundaryWalk (b : BoundaryDart M faces) {e : M.Dart}
    (he : IsBoundaryDart M faces e) (h : BoundaryWalk M faces b.1 e) :
    (boundaryPerm M faces b).1 = e :=
  boundaryWalk_eq_of_isBoundaryDart (boundaryPerm M faces b).2 he (boundaryPerm_walk M faces b) h

/-- **Every boundary circuit is a noncrossing closed walk.**  No planarity is used, and the face
set may have several circuits. -/
theorem circuit_isNoncrossingClosedWalk (c : Component M faces) :
    IsNoncrossingClosedWalk M (circuit M faces c) :=
  isNoncrossingClosedWalk_of_isChain_boundaryWalk (circuit_nonempty M faces c)
    (circuit_nodup M faces c)
    (fun d hd => ((mem_circuit_iff M faces c d).mp hd).elim fun h _ => h)
    (circuit_chain M faces c) (circuit_closes M faces c)

/-- **The circuit through a chained list.**  A list of boundary darts chained and closed by
boundary walks is closed under the boundary permutation, and the boundary permutation runs
through all of it.  So the circuit through any dart of the list has exactly the darts of the
list. -/
theorem mem_circuit_iff_of_isChain_boundaryWalk {w : List M.Dart} (hne : w ≠ [])
    (hbd : ∀ d ∈ w, IsBoundaryDart M faces d)
    (hchain : w.IsChain (BoundaryWalk M faces))
    (hclose : BoundaryWalk M faces (w.getLast hne) (w.head hne))
    {d₀ : M.Dart} (hd₀ : d₀ ∈ w) (d : M.Dart) :
    d ∈ circuit M faces (Quotient.mk'' ⟨d₀, hbd d₀ hd₀⟩) ↔ d ∈ w := by
  have hsucc : ∀ b : BoundaryDart M faces, b.1 ∈ w → (boundaryPerm M faces b).1 ∈ w := by
    intro b hb
    obtain ⟨e, he, hwalk⟩ := exists_mem_rel_of_isChain hne hchain hclose hb
    rw [boundaryPerm_val_of_boundaryWalk b (hbd e he) hwalk]
    exact he
  constructor
  · intro hd
    obtain ⟨h, hc⟩ := (mem_circuit_iff M faces _ d).mp hd
    have hsame : (boundaryPerm M faces).SameCycle ⟨d₀, hbd d₀ hd₀⟩ ⟨d, h⟩ :=
      Equiv.Perm.SameCycle.symm (Quotient.eq''.mp hc)
    obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
    have hpow : ∀ m : ℕ, ((boundaryPerm M faces ^ m) ⟨d₀, hbd d₀ hd₀⟩).1 ∈ w := by
      intro m
      induction m with
      | zero => exact hd₀
      | succ m ih =>
          rw [pow_succ', Perm.mul_apply]
          exact hsucc _ ih
    have hmem := hpow n
    rw [hn] at hmem
    exact hmem
  · intro hd
    have hlen : 0 < w.length := List.length_pos_iff.mpr hne
    have hmem : ∀ (i : ℕ) (hi : i < w.length), IsBoundaryDart M faces w[i] :=
      fun _ hi => hbd _ (List.getElem_mem hi)
    have key : ∀ (i : ℕ) (hi : i < w.length),
        (boundaryPerm M faces).SameCycle ⟨w[0], hmem 0 hlen⟩ ⟨w[i], hmem i hi⟩ := by
      intro i
      induction i with
      | zero => exact fun _ => Equiv.Perm.SameCycle.rfl
      | succ i ih =>
          intro hi
          have hi' : i < w.length := by omega
          have hstep : boundaryPerm M faces ⟨w[i], hmem i hi'⟩ = ⟨w[i + 1], hmem (i + 1) hi⟩ :=
            Subtype.ext (boundaryPerm_val_of_boundaryWalk ⟨w[i], hmem i hi'⟩ (hmem (i + 1) hi)
              (List.isChain_iff_getElem.mp hchain i (by omega)))
          rw [← hstep]
          exact Equiv.Perm.sameCycle_apply_right.mpr (ih hi')
    have hall : ∀ (a : M.Dart) (ha : a ∈ w),
        (boundaryPerm M faces).SameCycle ⟨w[0], hmem 0 hlen⟩ ⟨a, hbd a ha⟩ := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      exact key i hi
    exact (mem_circuit_iff M faces _ d).mpr
      ⟨hbd d hd, Quotient.sound' ((hall d hd).symm.trans (hall d₀ hd₀))⟩

end FaceSetCircuits

end Surgery.MapCollapse

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {faces : Finset Delta.toCombMap.Face}

/-- **A boundary step is a boundary walk.**  The elementary move `facePerm (alpha x)` from an
internal dart `x` is the rotation `sigma x`. -/
theorem boundaryWalk_of_boundaryStep {d e : Delta.toCombMap.Dart}
    (h : BoundaryStep Delta faces d e) :
    Surgery.MapCollapse.BoundaryWalk Delta.toCombMap faces d e := by
  obtain ⟨-, -, hmoves⟩ := h
  unfold Surgery.MapCollapse.BoundaryWalk
  induction hmoves with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih =>
      obtain ⟨hx, hax, rfl⟩ := hxy
      exact ih.tail
        ⟨⟨hx, hax⟩, (congrArg Delta.toCombMap.sigma (Delta.toCombMap.alpha_involutive _)).symm⟩

end Embedded

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryWalk.mono
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryWalk.trans_internal
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.BoundaryWalk.exists_pow
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.isNoncrossingClosedWalk_of_isChain_boundaryWalk
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits.boundaryPerm_val_of_boundaryWalk
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits.circuit_isNoncrossingClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.FaceSetCircuits.mem_circuit_iff_of_isChain_boundaryWalk
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.boundaryWalk_of_boundaryStep
