import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, lane gl-p06-06: face classes off the side of a walk

Infrastructure for lane gl-p06-06 of `carto-gl-p06` (Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b): the subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2` "contains all `Γ_{i,1}`'s").

Write `R` for `CombMap.FaceClassStep M (walkKeep M w)`: move around a face, or cross an edge off
the walk.  `sideFaces M w` is the set of faces whose darts are `R`-equivalent to a walk dart.

## Truth check and proof

* `not_walkKeep_of_internalDart`: an edge internal to `sideOutside M w` is off the walk, since a
  walk dart lies on a face of `sideFaces M w`.
* `eqvGen_of_boundaryWalk`: if every internal dart of `faces` is off `keep`, a boundary walk
  `facePerm d, σ, …, σ` through internal darts is an `R`-path: `x ↦ α x ↦ facePerm (α x) = σ x`.
* `eqvGen_of_mem_cycle`: along a boundary cycle that follows the boundary, consecutive darts are
  joined by boundary walks, so all cycle darts are `R`-equivalent (induction on the position,
  using `boundaryPerm_val_of_getElem` and `val_finRotate_of_lt`).
* `exists_alpha_mem_of_not_mem_sideFaces`: in a connected map with a nonempty walk, every
  `R`-class off `sideFaces M w` holds a dart `y` with `α y ∈ w`.  Otherwise no dart of the class
  is kept (a kept dart `y` of the class has `y ∉ w`, being off `sideFaces`, so `α y ∈ w`), and the
  class is closed under `α` and `σ = facePerm ∘ α` in both directions
  (`eqvGen_iff_of_adjacent`), hence is every dart, walk darts included: contradiction.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(b)); certifies no printed sentence.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial

universe v

open Surgery.MapCollapse SimpleClosedWalkSides

variable {M : CombMap.{v}}

/-- **An edge internal to the outside of a walk is off the walk.** -/
theorem not_walkKeep_of_internalDart {w : List M.Dart} {x : M.Dart}
    (hx : InternalDart M (sideOutside M w) x) : ¬ walkKeep M w x := by
  obtain ⟨hx₁, hx₂⟩ := hx
  rintro (hmem | hmem)
  · exact (mem_sideOutside_iff M w _).mp hx₁
      ((mem_sideFaces_iff M w x).mpr ⟨x, hmem, Relation.EqvGen.refl x⟩)
  · exact (mem_sideOutside_iff M w _).mp hx₂
      ((mem_sideFaces_iff M w (M.alpha x)).mpr ⟨M.alpha x, hmem, Relation.EqvGen.refl _⟩)

/-- **A boundary walk through internal darts off `keep` is a face-class path.** -/
theorem eqvGen_of_boundaryWalk {faces : Finset M.Face} {keep : M.Dart → Prop}
    (hint : ∀ x, InternalDart M faces x → ¬ keep x) {d e : M.Dart}
    (h : BoundaryWalk M faces d e) : Relation.EqvGen (CombMap.FaceClassStep M keep) d e := by
  have hstart : Relation.EqvGen (CombMap.FaceClassStep M keep) d (M.facePerm d) :=
    Relation.EqvGen.rel _ _ (Or.inl rfl)
  unfold BoundaryWalk at h
  induction h with
  | refl => exact hstart
  | @tail x _ _ hxy ih =>
      obtain ⟨hx, rfl⟩ := hxy
      refine Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.trans _ (M.alpha x) _
          (Relation.EqvGen.rel _ _ (Or.inr ⟨hint x hx, rfl⟩))
          (Relation.EqvGen.rel _ _ (Or.inl ?_)))
      show M.sigma x = M.sigma (M.alpha (M.alpha x))
      rw [M.alpha_involutive x]

/-- **All darts of a boundary cycle following the boundary lie in one face class**, when the
internal darts are off `keep`. -/
theorem eqvGen_of_mem_cycle {faces : Finset M.Face} {keep : M.Dart → Prop}
    (hint : ∀ x, InternalDart M faces x → ¬ keep x) {boundary : BoundaryCycle M faces}
    (hfollow : boundary.FollowsBoundary) {d e : M.Dart} (hd : d ∈ boundary.cycle)
    (he : e ∈ boundary.cycle) : Relation.EqvGen (CombMap.FaceClassStep M keep) d e := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
  have h0 : 0 < boundary.cycle.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have key : ∀ (k : ℕ) (hk : k < boundary.cycle.length),
      Relation.EqvGen (CombMap.FaceClassStep M keep) (boundary.cycle[0]'h0)
        (boundary.cycle[k]'hk) := by
    intro k
    induction k with
    | zero => intro _; exact Relation.EqvGen.refl _
    | succ k ih =>
        intro hk
        have hk' : k < boundary.cycle.length := Nat.lt_of_succ_lt hk
        have hb : IsBoundaryDart M faces (boundary.cycle[k]'hk') :=
          (boundary.cycle_mem_iff _).mp (List.getElem_mem hk')
        have hval := boundaryPerm_val_of_getElem M faces boundary k hk' ⟨_, hb⟩ rfl
        have hrot : finRotate boundary.cycle.length ⟨k, hk'⟩ = ⟨k + 1, hk⟩ :=
          Fin.ext (val_finRotate_of_lt _ hk)
        rw [hrot, List.get_eq_getElem] at hval
        have hwalk : BoundaryWalk M faces (boundary.cycle[k]'hk') (boundary.cycle[k + 1]'hk) := by
          have hw := hfollow ⟨_, hb⟩
          rw [hval] at hw
          exact hw
        exact Relation.EqvGen.trans _ _ _ (ih hk') (eqvGen_of_boundaryWalk hint hwalk)
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (key i hi)) (key j hj)

/-- **A face class with no kept dart is closed under both elementary moves.** -/
theorem eqvGen_iff_of_adjacent {w : List M.Dart} {x : M.Dart}
    (hnk : ∀ y, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x y →
      ¬ walkKeep M w y)
    {a b : M.Dart} (hab : M.Adjacent a b) :
    Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x a ↔
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x b := by
  have hfp : M.facePerm (M.alpha a) = M.sigma a := by
    show M.sigma (M.alpha (M.alpha a)) = M.sigma a
    rw [M.alpha_involutive a]
  rcases hab with rfl | rfl
  · constructor
    · intro ha
      exact Relation.EqvGen.trans _ _ _ ha (Relation.EqvGen.rel _ _ (Or.inr ⟨hnk a ha, rfl⟩))
    · intro hb
      have h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x
          (M.alpha (M.alpha a)) :=
        Relation.EqvGen.trans _ _ _ hb (Relation.EqvGen.rel _ _ (Or.inr ⟨hnk _ hb, rfl⟩))
      rwa [M.alpha_involutive a] at h
  · constructor
    · intro ha
      have hα : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x (M.alpha a) :=
        Relation.EqvGen.trans _ _ _ ha (Relation.EqvGen.rel _ _ (Or.inr ⟨hnk a ha, rfl⟩))
      have h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x
          (M.facePerm (M.alpha a)) :=
        Relation.EqvGen.trans _ _ _ hα (Relation.EqvGen.rel _ _ (Or.inl rfl))
      rwa [hfp] at h
    · intro hb
      have hα : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x (M.alpha a) :=
        Relation.EqvGen.trans _ _ _ hb
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl hfp.symm)))
      have h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x
          (M.alpha (M.alpha a)) :=
        Relation.EqvGen.trans _ _ _ hα (Relation.EqvGen.rel _ _ (Or.inr ⟨hnk _ hα, rfl⟩))
      rwa [M.alpha_involutive a] at h

/-- **Every face class off the side of a walk reaches the reversed walk**, in a connected map. -/
theorem exists_alpha_mem_of_not_mem_sideFaces (hM : M.IsConnected) {w : List M.Dart}
    (hne : w ≠ []) {x : M.Dart} (hx : M.faceOf x ∉ sideFaces M w) :
    ∃ y, M.alpha y ∈ w ∧ Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x y := by
  by_contra H
  have hnk : ∀ y, Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x y →
      ¬ walkKeep M w y := by
    rintro y hy (hmem | hmem)
    · exact hx ((mem_sideFaces_iff M w x).mpr ⟨y, hmem, Relation.EqvGen.symm _ _ hy⟩)
    · exact H ⟨y, hmem, hy⟩
  have hiff : ∀ a b, Relation.EqvGen M.Adjacent a b →
      (Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x a ↔
        Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) x b) := by
    intro a b hab
    induction hab with
    | rel _ _ h => exact eqvGen_iff_of_adjacent hnk h
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil w hne
  exact hnk d ((hiff x d (hM x d)).mp (Relation.EqvGen.refl x)) (Or.inl hd)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.not_walkKeep_of_internalDart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.eqvGen_of_boundaryWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.eqvGen_of_mem_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.eqvGen_iff_of_adjacent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Initial.exists_alpha_mem_of_not_mem_sideFaces
