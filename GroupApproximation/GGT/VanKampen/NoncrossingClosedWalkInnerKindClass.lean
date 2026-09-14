import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkVertexKind
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# The vertex classifier of the inner reclosing, by the kind of the vertex

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

Let `w` be a noncrossing closed walk whose passages have free sectors.  At a vertex with an adjacent
passage every passage is adjacent (`IsNoncrossingClosedWalk.passageAdjacent_of_vertex`), and the inner
reclosing has one vertex for each of them: rotating from a retained dart, the first reversal
`alpha w[l]` of a walk dart names the vertex.  At any other vertex the inner reclosing has at most one
vertex.  This module defines the classifier and characterizes its values; its invariance and the count
are in later modules.

* `IsNoncrossingClosedWalk.AdjVertex`: a vertex holding an adjacent passage.
* `IsNoncrossingClosedWalk.InnerKindIndex`: the vertices without adjacent passage that carry a retained
  inner dart, and the adjacent passages.
* `IsNoncrossingClosedWalk.exists_first_adjacent`: at a vertex with an adjacent passage, rotation from a
  dart meets a first reversal of a walk dart, and its passage is adjacent.
* `IsNoncrossingClosedWalk.innerKindClass` with `innerKindClass_eq_inr` and `innerKindClass_eq_inl`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides SectorNoninterleaving NoncrossingClosedWalkEuler

universe u

namespace IsNoncrossingClosedWalk

/-- **A vertex holding an adjacent passage.** -/
def AdjVertex (M : CombMap.{u}) (w : List M.Dart) (c : M.Vertex) : Prop :=
  ∃ i : Fin w.length, M.vertexOf (M.alpha (w.get i)) = c ∧ PassageAdjacent M w i

/-- **The vertices of the inner reclosing, by kind**: a vertex without adjacent passage carrying a
retained inner dart, or an adjacent passage. -/
abbrev InnerKindIndex (M : CombMap.{u}) (w : List M.Dart) : Type u :=
  {c : M.Vertex // ¬ AdjVertex M w c ∧ ∃ x : KeptDart M (sideFaces M w), M.vertexOf x.1 = c} ⊕
    {i : Fin w.length // PassageAdjacent M w i}

variable {M : CombMap.{u}} {w : List M.Dart}

private theorem vertexOf_sigma_pow' (M : CombMap.{u}) (n : ℕ) (d : M.Dart) :
    M.vertexOf ((M.sigma ^ n) d) = M.vertexOf d := by
  induction n with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ n ih => rw [pow_succ', Perm.mul_apply, M.vertexOf_sigma, ih]

/-- **At a vertex with an adjacent passage, the first reversal met from any dart names an adjacent
passage.** -/
theorem exists_first_adjacent (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    {x : M.Dart} (h : AdjVertex M w (M.vertexOf x)) :
    ∃ l : Fin w.length, PassageAdjacent M w l ∧ ∃ m : ℕ, (M.sigma ^ m) x = M.alpha (w.get l) ∧
      ∀ j < m, M.alpha ((M.sigma ^ j) x) ∉ w := by
  obtain ⟨i, hi, hadj⟩ := h
  obtain ⟨k, hk⟩ := ((M.vertexOf_eq_iff x (M.alpha (w.get i))).mp hi.symm).exists_nat_pow_eq
  have hhit : ∃ k : ℕ, M.alpha ((M.sigma ^ k) x) ∈ w :=
    ⟨k, by rw [hk, M.alpha_involutive]; exact List.get_mem w i⟩
  obtain ⟨m, hm, hmin⟩ := exists_first_hit hhit
  obtain ⟨l, hl⟩ := List.get_of_mem hm
  have hml : (M.sigma ^ m) x = M.alpha (w.get l) := by rw [hl, M.alpha_involutive]
  have hvl : M.vertexOf (M.alpha (w.get l)) = M.vertexOf (M.alpha (w.get i)) := by
    rw [← hml, hi]
    exact vertexOf_sigma_pow' M m x
  exact ⟨l, hw.passageAdjacent_of_vertex hM hsector hadj hvl, m, hml, hmin⟩

open Classical in
/-- **The classifier of the inner reclosing, by kind.**  A retained inner dart at a vertex with an
adjacent passage goes to the first adjacent passage met by rotation; any other goes to its vertex. -/
noncomputable def innerKindClass (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    (x : KeptDart M (sideFaces M w)) : InnerKindIndex M w :=
  if h : AdjVertex M w (M.vertexOf x.1) then
    Sum.inr ⟨Classical.choose (hw.exists_first_adjacent hM hsector h),
      (Classical.choose_spec (hw.exists_first_adjacent hM hsector h)).1⟩
  else Sum.inl ⟨M.vertexOf x.1, h, x, rfl⟩

/-- **The class at a vertex with an adjacent passage is the first reversal met.** -/
theorem innerKindClass_eq_inr (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    (x : KeptDart M (sideFaces M w)) (h : AdjVertex M w (M.vertexOf x.1)) {l : Fin w.length}
    (hl : PassageAdjacent M w l) {m : ℕ} (hml : (M.sigma ^ m) x.1 = M.alpha (w.get l))
    (hmin : ∀ j < m, M.alpha ((M.sigma ^ j) x.1) ∉ w) :
    hw.innerKindClass hM hsector x = Sum.inr ⟨l, hl⟩ := by
  unfold innerKindClass
  rw [dif_pos h]
  obtain ⟨-, m', hm', hmin'⟩ := Classical.choose_spec (hw.exists_first_adjacent hM hsector h)
  have hP : ∀ {n : ℕ} {l' : Fin w.length}, (M.sigma ^ n) x.1 = M.alpha (w.get l') →
      M.alpha ((M.sigma ^ n) x.1) ∈ w := fun {n l'} hn => by
    rw [hn, M.alpha_involutive]
    exact List.get_mem w l'
  have hmm := first_unique (P := fun n => M.alpha ((M.sigma ^ n) x.1) ∈ w) (hP hm') hmin' (hP hml)
    hmin
  rw [hmm, hml] at hm'
  exact congrArg Sum.inr (Subtype.ext (hw.nodup.get_inj_iff.mp (M.alpha.injective hm'.symm)))

/-- **The class at a vertex without adjacent passage is the vertex.** -/
theorem innerKindClass_eq_inl (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    (x : KeptDart M (sideFaces M w)) (h : ¬ AdjVertex M w (M.vertexOf x.1)) :
    hw.innerKindClass hM hsector x = Sum.inl ⟨M.vertexOf x.1, h, x, rfl⟩ := by
  unfold innerKindClass
  rw [dif_neg h]

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.exists_first_adjacent
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.innerKindClass_eq_inr
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.innerKindClass_eq_inl
