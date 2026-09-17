import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.InPlace
import GroupApproximation.Meta.AxiomGuard

/-!
# Walk rotations and region moves for the rose step

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  This module collects two pieces of list and face-set infrastructure used
by the live rose reduction chain: the rotation lemma behind `inPlaceStep_of_regionMoveSubArc`, and
the face-flipping moves behind the sub-arc region move (`RoseRegionMoveSubArcStatement`) and the
single-region move built on it.  It imports only `P10Rose/InPlace`.

## Rotations (`FilterWalk`)

Let `p` be a Boolean predicate on a list.

1. *A true member followed by a false member* (`exists_pair_of_head`, `exists_pair_of_getLast`).  If
   a list `a :: l` has a false member and `p a = true`, walk forward from `a`: the first false member
   has a true predecessor, so `a :: l = P ++ x :: z :: Q` with `p x = true`, `p z = false`.  If the
   list has a true member and ends in a false member, walk backwards in the same way.
2. *The rotation of a split pair* (`exists_rotation_of_pair`): `P ++ x :: z :: Q` rotates to
   `(z :: Q) ++ (P ++ [x])`, which ends in `x` and starts with `z`.
3. *A rotation ending in a true member and starting with a false member* (`exists_rotation`).  Write
   `l = a :: t`.  If the last member is false, (1) gives `P ++ x :: z :: Q` and (2) rotates it.  If
   the last member is true and `p a` is false, the list itself is such a rotation.  If both are
   true, (1) from the head gives the pair.

In `inPlaceStep_of_regionMoveSubArc` the list is the old boundary cycle and `p` is the kept-dart
predicate `movePred M z` of a move: the rotation ends in a kept dart `e` and starts with a removed
dart `f`, so `α e` ends where `f` begins, and the successor of `e` in the new closed walk begins
there too.  This is the kept dart sharing its vertex with a removed dart.

## Region moves (`FilterMove`)

Let `M` be a combinatorial map, `F` a finite set of faces and `c` a list whose members are exactly
the boundary darts of `F` (a `BoundaryCycle`).  Call the classes of the relation
`FaceClassStep M (walkKeep M c)` (move around a face, or cross an edge off `c`) *regions*.  A
*move* is a dart colouring `z : Dart → Bool` constant on regions (constant along each step); `z = true`
marks the regions to flip.  Put

* `flipFaces M F z = {f | f ∈ F ↔ z = false on f}`, the symmetric difference of `F` with the union
  of the flipped regions (`flipFaces`); membership is read off any dart of `f` because `z` is
  constant along `facePerm` (`mem_flipFaces_iff`, from `eqvGen_faceClass_of_sameCycle`);
* `movePred M z d = !z d && !z (α d)`: neither side of `d` is flipped (`movePred`).

1. *Faces.*  A face on which `z` is `false` keeps its membership in `F` (`not_mem_flipFaces`,
   `mem_flipFaces`).  So the exterior face and the source cell stay out, and the kept cell stays in,
   when `z` vanishes on them.
2. *Boundary* (`isBoundaryDart_flipFaces_iff`).  Suppose that no dart of `c` has both sides flipped.
   Then the boundary darts of `flipFaces M F z` are exactly the darts `d ∈ c` with
   `movePred M z d = true`.
   * If `d ∈ c`, then `face d ∈ F` and `face (α d) ∉ F`; `d` is a boundary dart of the new set iff
     `z d = false` (so `face d` stays in) and `z (α d) = false` (so `face (α d)` stays out).
   * If `α d ∈ c`, then `face d ∉ F` and `face (α d) ∈ F`; `d` would be a boundary dart only if
     both sides of `α d` are flipped, which is excluded.
   * Otherwise `d` and `α d` are joined by a step, so `z d = z (α d)`, and `face d ∈ F ↔
     face (α d) ∈ F` (`faceOf_mem_iff_of_walkEqvGen`); hence both faces are in the new set or both
     are out, and `d` is not a boundary dart.
3. *Arcs.*  A dart of the target arc `t_2` has the exterior face across it, and a dart of the
   reversed source arc `t_1⁻¹` has the source cell across it (`faceOf_alpha_of_mem_targetArc`,
   `faceOf_alpha_of_mem_invSourceArc`).  If `z` vanishes on these darts and on those two faces,
   `movePred` keeps them.

In the sub-arc region move, `F' = flipFaces M F z` is the new face set and its boundary is the old
cycle filtered by `movePred M z` (item 2), re-listed by a permutation as a closed walk with new
proper arcs; items 1 and 3 keep the exterior face and the source cell out and the kept cell in.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

namespace FilterWalk

/-- **A true member followed by a false one**, walking forward from a true head. -/
theorem exists_pair_of_head {α : Type*} (p : α → Bool) (a : α) (l : List α) (ha : p a = true)
    (hy : ∃ y ∈ a :: l, p y = false) :
    ∃ (P : List α) (x z : α) (Q : List α),
      a :: l = P ++ x :: z :: Q ∧ p x = true ∧ p z = false := by
  induction l generalizing a with
  | nil =>
    obtain ⟨y, hy, hpy⟩ := hy
    rw [List.mem_singleton] at hy
    rw [hy, ha] at hpy
    cases hpy
  | cons b l ih =>
    obtain ⟨y, hy, hpy⟩ := hy
    cases hb : p b with
    | false => exact ⟨[], a, b, l, rfl, ha, hb⟩
    | true =>
      have hy' : y ∈ b :: l := by
        rcases List.mem_cons.mp hy with h | h
        · rw [h, ha] at hpy
          cases hpy
        · exact h
      obtain ⟨P, x, z, Q, hPQ, hx, hz⟩ := ih b hb ⟨y, hy', hpy⟩
      exact ⟨a :: P, x, z, Q, by rw [hPQ, List.cons_append], hx, hz⟩

/-- **A true member followed by a false one**, walking backwards from a false last member. -/
theorem exists_pair_of_getLast {α : Type*} (p : α → Bool) (a : α) (l : List α)
    (hx : ∃ x ∈ a :: l, p x = true)
    (hlast : p ((a :: l).getLast (List.cons_ne_nil a l)) = false) :
    ∃ (P : List α) (x z : α) (Q : List α),
      a :: l = P ++ x :: z :: Q ∧ p x = true ∧ p z = false := by
  induction l generalizing a with
  | nil =>
    obtain ⟨x, hx, hpx⟩ := hx
    rw [List.mem_singleton] at hx
    have ha : p a = false := hlast
    rw [hx, ha] at hpx
    cases hpx
  | cons b l ih =>
    have hlast' : p ((b :: l).getLast (List.cons_ne_nil b l)) = false := hlast
    cases ha : p a with
    | true =>
      cases hb : p b with
      | false => exact ⟨[], a, b, l, rfl, ha, hb⟩
      | true =>
        obtain ⟨P, x, z, Q, hPQ, hpx, hz⟩ := ih b ⟨b, List.mem_cons_self, hb⟩ hlast'
        exact ⟨a :: P, x, z, Q, by rw [hPQ, List.cons_append], hpx, hz⟩
    | false =>
      obtain ⟨x, hx, hpx⟩ := hx
      have hx' : x ∈ b :: l := by
        rcases List.mem_cons.mp hx with h | h
        · rw [h, ha] at hpx
          cases hpx
        · exact h
      obtain ⟨P, c, z, Q, hPQ, hpc, hz⟩ := ih b ⟨x, hx', hpx⟩ hlast'
      exact ⟨a :: P, c, z, Q, by rw [hPQ, List.cons_append], hpc, hz⟩

/-- **The rotation of a split pair**: `P ++ x :: z :: Q` rotates to `(z :: Q) ++ (P ++ [x])`,
which ends in `x` and starts with `z`. -/
theorem exists_rotation_of_pair {α : Type*} (p : α → Bool) {l : List α} (P : List α)
    (x z : α) (Q : List α) (hl : l = P ++ x :: z :: Q) (hx : p x = true) (hz : p z = false) :
    ∃ (A B : List α) (hne : B ++ A ≠ []), l = A ++ B ∧
      p ((B ++ A).getLast hne) = true ∧ p ((B ++ A).head hne) = false := by
  refine ⟨P ++ [x], z :: Q,
    List.append_ne_nil_of_right_ne_nil (z :: Q)
      (List.append_ne_nil_of_right_ne_nil P (List.cons_ne_nil x [])),
    hl.trans (by simp), ?_, hz⟩
  rw [List.getLast_append_of_ne_nil _
      (List.append_ne_nil_of_right_ne_nil P (List.cons_ne_nil x [])),
    List.getLast_append_of_ne_nil _ (List.cons_ne_nil x []), List.getLast_singleton]
  exact hx

/-- **A rotation ending in a true member and starting with a false member.**  Used in
`inPlaceStep_of_regionMoveSubArc` with `p = movePred M z` on the old boundary cycle. -/
theorem exists_rotation {α : Type*} (p : α → Bool) {l : List α} {x y : α} (hx : x ∈ l)
    (hpx : p x = true) (hy : y ∈ l) (hpy : p y = false) :
    ∃ (A B : List α) (hne : B ++ A ≠ []), l = A ++ B ∧
      p ((B ++ A).getLast hne) = true ∧ p ((B ++ A).head hne) = false := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hy)
  cases hlast : p ((a :: t).getLast (List.cons_ne_nil a t)) with
  | false =>
    obtain ⟨P, c, z, Q, hl, hc, hz⟩ := exists_pair_of_getLast p a t ⟨x, hx, hpx⟩ hlast
    exact exists_rotation_of_pair p P c z Q hl hc hz
  | true =>
    cases ha : p a with
    | false => exact ⟨a :: t, [], List.cons_ne_nil a t, (List.append_nil _).symm, hlast, ha⟩
    | true =>
      obtain ⟨P, c, z, Q, hl, hc, hz⟩ := exists_pair_of_head p a t ha ⟨y, hy, hpy⟩
      exact exists_rotation_of_pair p P c z Q hl hc hz

end FilterWalk

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

namespace FilterMove

/-- **The kept darts of a move**: neither side is flipped. -/
def movePred (M : CombMap.{v}) (z : M.Dart → Bool) (d : M.Dart) : Bool :=
  !z d && !z (M.alpha d)

theorem movePred_eq_true_iff (M : CombMap.{v}) (z : M.Dart → Bool) (d : M.Dart) :
    movePred M z d = true ↔ z d = false ∧ z (M.alpha d) = false := by
  cases hd : z d <;> cases ha : z (M.alpha d) <;> simp [movePred, hd, ha]

/-- **The face set after a move**: the faces whose membership in `faces` agrees with `z = false`. -/
noncomputable def flipFaces (M : CombMap.{v}) (faces : Finset M.Face) (z : M.Dart → Bool) :
    Finset M.Face := by
  classical
  exact Finset.univ.filter fun f => ∃ x, M.faceOf x = f ∧ (M.faceOf x ∈ faces ↔ z x = false)

/-- A Boolean function constant along a relation is constant along its equivalence closure. -/
theorem eq_of_eqvGen {α : Type*} {r : α → α → Prop} {z : α → Bool}
    (hz : ∀ x y, r x y → z x = z y) {x y : α} (h : Relation.EqvGen r x y) : z x = z y := by
  induction h with
  | rel a₁ a₂ hab => exact hz a₁ a₂ hab
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Membership after a move**, read off any dart of the face. -/
theorem mem_flipFaces_iff {M : CombMap.{v}} {faces : Finset M.Face} {keep : M.Dart → Prop}
    {z : M.Dart → Bool} (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y)
    (x : M.Dart) :
    M.faceOf x ∈ flipFaces M faces z ↔ (M.faceOf x ∈ faces ↔ z x = false) := by
  classical
  unfold flipFaces
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, y, hy, h⟩
    rwa [hy, eq_of_eqvGen hz
      (eqvGen_faceClass_of_sameCycle M keep ((M.faceOf_eq_iff y x).mp hy))] at h
  · intro h
    exact ⟨Finset.mem_univ _, x, rfl, h⟩

/-- An unflipped face outside the face set stays outside. -/
theorem not_mem_flipFaces {M : CombMap.{v}} {faces : Finset M.Face} {keep : M.Dart → Prop}
    {z : M.Dart → Bool} (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y)
    {f : M.Face} (hf : f ∉ faces) (hzf : ∀ x, M.faceOf x = f → z x = false) :
    f ∉ flipFaces M faces z := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep f
  intro h
  exact hf (((mem_flipFaces_iff hz x).mp h).mpr (hzf x rfl))

/-- An unflipped face inside the face set stays inside. -/
theorem mem_flipFaces {M : CombMap.{v}} {faces : Finset M.Face} {keep : M.Dart → Prop}
    {z : M.Dart → Bool} (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y)
    {f : M.Face} (hf : f ∈ faces) (hzf : ∀ x, M.faceOf x = f → z x = false) :
    f ∈ flipFaces M faces z := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep f
  exact (mem_flipFaces_iff hz x).mpr ⟨fun _ => hzf x rfl, fun _ => hf⟩

/-- The boundary darts of the moved face set on the old cycle. -/
theorem isBoundaryDart_flipFaces_of_mem {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} {z : M.Dart → Bool}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {d : M.Dart}
    (hdc : d ∈ c) :
    ((M.faceOf d ∈ faces ↔ z d = false) ∧ ¬(M.faceOf (M.alpha d) ∈ faces ↔
      z (M.alpha d) = false)) ↔ d ∈ c ∧ z d = false ∧ z (M.alpha d) = false := by
  obtain ⟨hin, hout⟩ := (hc d).mp hdc
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hdc, h1.mp hin, ?_⟩
    by_contra h3
    exact h2 ⟨fun h => absurd h hout, fun h => absurd h h3⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨⟨fun _ => h1, fun _ => hin⟩, fun h => hout (h.mpr h2)⟩

/-- A dart off the old cycle is not a boundary dart of the moved face set. -/
theorem not_isBoundaryDart_flipFaces_of_not_mem {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} {z : M.Dart → Bool}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) {d : M.Dart} (hdc : d ∉ c)
    (h1 : M.faceOf d ∈ faces ↔ z d = false)
    (h2 : ¬(M.faceOf (M.alpha d) ∈ faces ↔ z (M.alpha d) = false)) : False := by
  by_cases hac : M.alpha d ∈ c
  · obtain ⟨hin, hout⟩ := (hc _).mp hac
    rw [M.alpha_involutive d] at hout
    have hzd : z d ≠ false := fun h => hout (h1.mpr h)
    have hza : z (M.alpha d) ≠ false := fun h => h2 ⟨fun _ => h, fun _ => hin⟩
    rcases hind _ hac with h | h
    · exact hza h
    · rw [M.alpha_involutive d] at h
      exact hzd h
  · have hstep : CombMap.FaceClassStep M (walkKeep M c) d (M.alpha d) :=
      Or.inr ⟨fun hk => Or.elim hk hdc hac, rfl⟩
    have hzeq := hz d (M.alpha d) hstep
    have hfeq := faceOf_mem_iff_of_walkEqvGen hc (Relation.EqvGen.rel _ _ hstep)
    rw [← hzeq, ← hfeq] at h2
    exact h2 h1

/-- **The boundary of the moved face set** is the old cycle filtered by `movePred`, when no dart of
the cycle has both sides flipped. -/
theorem isBoundaryDart_flipFaces_iff {M : CombMap.{v}} {faces : Finset M.Face}
    {c : List M.Dart} {z : M.Dart → Bool}
    (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false) (d : M.Dart) :
    Surgery.MapCollapse.IsBoundaryDart M (flipFaces M faces z) d ↔
      d ∈ c ∧ movePred M z d = true := by
  rw [movePred_eq_true_iff]
  show M.faceOf d ∈ flipFaces M faces z ∧ M.faceOf (M.alpha d) ∉ flipFaces M faces z ↔ _
  rw [mem_flipFaces_iff hz, mem_flipFaces_iff hz]
  by_cases hdc : d ∈ c
  · exact isBoundaryDart_flipFaces_of_mem hc hdc
  · refine ⟨fun h => ?_, fun h => absurd h.1 hdc⟩
    exact (not_isBoundaryDart_flipFaces_of_not_mem hc hz hind hdc h.1 h.2).elim

section Arcs

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- Across a dart of the target arc lies the exterior face. -/
theorem faceOf_alpha_of_mem_targetArc (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.targetArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace := by
  have hmem : d ∈ outerDarts X := K.targetArc.mem_cycle_of_mem_darts hd
  simp only [outerDarts, List.mem_map, List.mem_reverse] at hmem
  obtain ⟨e, he, rfl⟩ := hmem
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary X.outerFace).mem_iff e).mp he

/-- Across a dart of the reversed source arc lies the source cell. -/
theorem faceOf_alpha_of_mem_invSourceArc (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X K.sourceArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X K.source).face := by
  simp only [invDarts, List.mem_map, List.mem_reverse] at hd
  obtain ⟨e, he, rfl⟩ := hd
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary (cell X K.source).face).mem_iff e).mp
    (K.sourceArc.mem_cycle_of_mem_darts he)

end Arcs

end FilterMove

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_pair_of_head
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_pair_of_getLast
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_rotation_of_pair
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterWalk.exists_rotation
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.movePred
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.movePred_eq_true_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.flipFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.eq_of_eqvGen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.mem_flipFaces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.not_mem_flipFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.mem_flipFaces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.isBoundaryDart_flipFaces_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.not_isBoundaryDart_flipFaces_of_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.isBoundaryDart_flipFaces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.faceOf_alpha_of_mem_targetArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.FilterMove.faceOf_alpha_of_mem_invSourceArc
