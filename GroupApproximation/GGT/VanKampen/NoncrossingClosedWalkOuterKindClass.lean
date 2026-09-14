import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkInnerKindClass
import GroupApproximation.Meta.AxiomGuard

/-!
# The vertex classifier of the outer reclosing, by the kind of the vertex

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

Let `w` be a noncrossing closed walk whose passages have free sectors.  At a vertex touched by the walk
without adjacent passage, every passage is short, and the outer reclosing has one vertex for each of
them: rotating from a retained outer dart, the first walk dart `w[l+1]` names the passage `l`.  At an
untouched vertex, and at a vertex with an adjacent passage, the outer reclosing has at most one vertex.
This module defines the classifier and characterizes its values.

* `IsNoncrossingClosedWalk.Touched`: a vertex where some passage turns.
* `IsNoncrossingClosedWalk.OuterKindIndex`: the untouched or adjacent vertices carrying a retained outer
  dart, and the passages that are not adjacent.
* `IsNoncrossingClosedWalk.exists_first_short`: at a touched vertex without adjacent passage, rotation
  from a dart meets a first walk dart, and the passage ending there is not adjacent.
* `IsNoncrossingClosedWalk.outerKindClass` with `outerKindClass_eq_inr` and `outerKindClass_eq_inl`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides SectorNoninterleaving NoncrossingClosedWalkEuler

universe u

namespace IsNoncrossingClosedWalk

/-- **A vertex where some passage turns.** -/
def Touched (M : CombMap.{u}) (w : List M.Dart) (c : M.Vertex) : Prop :=
  ∃ i : Fin w.length, M.vertexOf (M.alpha (w.get i)) = c

/-- **The vertices of the outer reclosing, by kind**: an untouched or adjacent vertex carrying a
retained outer dart, or a passage that is not adjacent. -/
abbrev OuterKindIndex (M : CombMap.{u}) (w : List M.Dart) : Type u :=
  {c : M.Vertex // (¬ Touched M w c ∨ AdjVertex M w c) ∧
      ∃ x : KeptDart M (sideOutside M w), M.vertexOf x.1 = c} ⊕
    {i : Fin w.length // ¬ PassageAdjacent M w i}

variable {M : CombMap.{u}} {w : List M.Dart}

private theorem vertexOf_sigma_pow'' (M : CombMap.{u}) (n : ℕ) (d : M.Dart) :
    M.vertexOf ((M.sigma ^ n) d) = M.vertexOf d := by
  induction n with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ n ih => rw [pow_succ', Perm.mul_apply, M.vertexOf_sigma, ih]

/-- **At a touched vertex without adjacent passage, the first walk dart met names a passage that is
not adjacent.** -/
theorem exists_first_short (hw : IsNoncrossingClosedWalk M w) {x : M.Dart}
    (hT : Touched M w (M.vertexOf x)) (hA : ¬ AdjVertex M w (M.vertexOf x)) :
    ∃ l : Fin w.length, ¬ PassageAdjacent M w l ∧
      ∃ m : ℕ, (M.sigma ^ m) x = w.get (finRotate w.length l) ∧ ∀ j < m, (M.sigma ^ j) x ∉ w := by
  obtain ⟨i, hi⟩ := hT
  have hvi : M.vertexOf (w.get (finRotate w.length i)) = M.vertexOf x :=
    (get_finRotate_of_isChain_closes hw.ne_nil hw.chain hw.closes i).symm.trans hi
  obtain ⟨k, hk⟩ := ((M.vertexOf_eq_iff x _).mp hvi.symm).exists_nat_pow_eq
  have hhit : ∃ k : ℕ, (M.sigma ^ k) x ∈ w := ⟨k, by rw [hk]; exact List.get_mem w _⟩
  obtain ⟨m, hm, hmin⟩ := exists_first_of_exists hhit
  obtain ⟨p, hp⟩ := List.get_of_mem hm
  refine ⟨(finRotate w.length).symm p, fun hadj => hA ?_, m, ?_, hmin⟩
  · refine ⟨(finRotate w.length).symm p, ?_, hadj⟩
    rw [get_finRotate_of_isChain_closes hw.ne_nil hw.chain hw.closes, Equiv.apply_symm_apply, hp,
      vertexOf_sigma_pow'' M m x]
  · rw [Equiv.apply_symm_apply, hp]

open Classical in
/-- **The classifier of the outer reclosing, by kind.**  A retained outer dart at a touched vertex
without adjacent passage goes to the passage ending at the first walk dart met by rotation; any other
goes to its vertex. -/
noncomputable def outerKindClass (hw : IsNoncrossingClosedWalk M w)
    (x : KeptDart M (sideOutside M w)) : OuterKindIndex M w :=
  if h : Touched M w (M.vertexOf x.1) ∧ ¬ AdjVertex M w (M.vertexOf x.1) then
    Sum.inr ⟨Classical.choose (hw.exists_first_short h.1 h.2),
      (Classical.choose_spec (hw.exists_first_short h.1 h.2)).1⟩
  else Sum.inl ⟨M.vertexOf x.1, (not_and_or.mp h).imp id not_not.mp, x, rfl⟩

/-- **The class at a touched vertex without adjacent passage is the passage ending at the first walk
dart met.** -/
theorem outerKindClass_eq_inr (hw : IsNoncrossingClosedWalk M w)
    (x : KeptDart M (sideOutside M w))
    (h : Touched M w (M.vertexOf x.1) ∧ ¬ AdjVertex M w (M.vertexOf x.1)) {l : Fin w.length}
    (hl : ¬ PassageAdjacent M w l) {m : ℕ}
    (hml : (M.sigma ^ m) x.1 = w.get (finRotate w.length l))
    (hmin : ∀ j < m, (M.sigma ^ j) x.1 ∉ w) :
    hw.outerKindClass x = Sum.inr ⟨l, hl⟩ := by
  unfold outerKindClass
  rw [dif_pos h]
  obtain ⟨-, m', hm', hmin'⟩ := Classical.choose_spec (hw.exists_first_short h.1 h.2)
  have hP : ∀ {n : ℕ} {l' : Fin w.length},
      (M.sigma ^ n) x.1 = w.get (finRotate w.length l') → (M.sigma ^ n) x.1 ∈ w :=
    fun {n l'} hn => by rw [hn]; exact List.get_mem w _
  have hmm := first_unique (P := fun n => (M.sigma ^ n) x.1 ∈ w) (hP hm') hmin' (hP hml) hmin
  rw [hmm, hml] at hm'
  exact congrArg Sum.inr (Subtype.ext
    ((finRotate w.length).injective (hw.nodup.get_inj_iff.mp hm'.symm)))

/-- **The class at an untouched or adjacent vertex is the vertex.** -/
theorem outerKindClass_eq_inl (hw : IsNoncrossingClosedWalk M w)
    (x : KeptDart M (sideOutside M w))
    (h : ¬ (Touched M w (M.vertexOf x.1) ∧ ¬ AdjVertex M w (M.vertexOf x.1))) :
    hw.outerKindClass x =
      Sum.inl ⟨M.vertexOf x.1, (not_and_or.mp h).imp id not_not.mp, x, rfl⟩ := by
  unfold outerKindClass
  rw [dif_neg h]

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.exists_first_short
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.outerKindClass_eq_inr
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.outerKindClass_eq_inl
