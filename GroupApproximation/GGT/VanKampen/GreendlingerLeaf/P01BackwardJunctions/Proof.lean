import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BoundaryJunctionBudget
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94JunctionPocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: at most `n + 1` backward junctions

Target: `OsinLemma94BackwardJunctionCountInput`.  Summed over the relator polygons, the backward
boundary junctions number at most `n + 1`, where `n` is the number of relator cells.

## Route

Write `w = outerDarts Δ` (length `m`), `M` for the map of `Δ`, `O` for the outer face.  The
outer walk satisfies `σ w[q+1] = α w[q]` (the face chain of `O`, reversed and reflected by `α`),
`w` has no repeated darts, and `faceOf (α w[q]) = O`.

A backward junction `s` of polygon `k` gives darts `e` (last dart of side `s`) and `e'` (first
dart of the next side), both on `w`, with `facePerm e = e'`, i.e. `σ (α w[a]) = w[b]`, where
`a = idxOf e`, `b = idxOf e'` and `b ≤ a`.  Call it *degenerate* when `e = w[m-1]`.

1. **Pocket.**  Take a non-degenerate junction `(a, b)`, so `a + 1 < m`.  The darts
   `p = α w[b]` and `q = α w[a+1]` lie on `O` and `σ` has `α p = w[b]` and
   `α q = w[a+1]` in one cycle (`σ² w[a+1] = w[b]`).  `JunctionPocket.not_reach` says
   `facePerm p` and `facePerm q` are apart in the joined map.  `facePerm q = α w[a]` is next to
   `w[a]`.  For every `c < b` or `c > a`, the dart `w[c]` is reached from `facePerm p`: walking
   along `w` by `α` and `σ` never touches `α p, α q` outside `[b, a+1]`, and the joined map
   turns `w[a+1]` into `facePerm p` (`not_reach_outside`).  So `w[a]` does not reach `w[c]`.
2. **Cell link.**  If two junctions `(a, b)` and `(c, d)` belong to polygons with a common
   relator cell `j`, then `w[a]` reaches `w[c]` in every join at two darts of `O`: go inside
   polygon face, cross to cell `j` and back (`reach_via_cell`).  With step 1 in both directions
   `b ≤ c ≤ a` and `d ≤ a ≤ c`, so `a = c` (`index_eq`).
3. **Count.**  Label a junction by `none` when degenerate, else by the first cell of its polygon.
   Equal labels force equal last darts `e`, and `e` determines polygon and side (the face of
   `e`, disjoint sides).  So the junctions inject into `Option (Fin n)`, of size `n + 1`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01BackwardJunctions

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

section Pocket

variable {M : CombMap.{v}} [DecidableEq M.Dart]

/-- Walking backward along the outer walk in the joined map, away from the joined darts. -/
theorem reach_chain {f : ℕ → M.Dart} {m : ℕ}
    (hstep : ∀ q, q + 1 < m → M.sigma (f (q + 1)) = M.alpha (f q)) {p e : M.Dart} (i : ℕ) :
    ∀ d, i + d < m → (∀ q, i < q → q ≤ i + d → f q ≠ M.alpha p ∧ f q ≠ M.alpha e) →
      Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.alpha (f (i + d))) (M.alpha (f i)) := by
  intro d
  induction d with
  | zero =>
      intro _ _
      exact Relation.EqvGen.refl _
  | succ d ih =>
      intro hd hq
      have hq' := hq (i + d + 1) (by omega) (by omega)
      have h1 : Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.alpha (f (i + d + 1)))
          (f (i + d + 1)) :=
        Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive (f (i + d + 1))))
      have h2 : Relation.EqvGen (FoldMap.joined M p e).Adjacent (f (i + d + 1))
          (M.alpha (f (i + d))) :=
        Relation.EqvGen.rel _ _
          (Or.inr ((JunctionPocket.joined_sigma_apply_of_ne hq'.1 hq'.2).trans
            (hstep (i + d) (by omega))))
      exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.trans _ _ _ h2
        (ih (by omega) fun q hq1 hq2 => hq q hq1 (by omega)))

/-- Outside the pocket `[b, a]`, every outer dart is reached from `facePerm (α w[b])`. -/
theorem reach_outside {f : ℕ → M.Dart} {m : ℕ}
    (hstep : ∀ q, q + 1 < m → M.sigma (f (q + 1)) = M.alpha (f q))
    (hinj : ∀ i j, i < m → j < m → f i = f j → i = j)
    {a b c : ℕ} (hba : b ≤ a) (ham : a + 1 < m) (hcm : c < m) (hc : c < b ∨ a < c) :
    Relation.EqvGen (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).Adjacent
      (M.facePerm (M.alpha (f b))) (f c) := by
  have hcα : Relation.EqvGen (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).Adjacent
      (M.alpha (f c)) (f c) := Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive (f c)))
  rcases hc with hcb | hac
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hfp : M.facePerm (M.alpha (f (b' + 1))) = M.alpha (f b') := by
      show M.sigma (M.alpha (M.alpha (f (b' + 1)))) = M.alpha (f b')
      rw [M.alpha_involutive (f (b' + 1))]
      exact hstep b' (by omega)
    have hch := reach_chain hstep (p := M.alpha (f (b' + 1))) (e := M.alpha (f (a + 1))) c (b' - c)
      (by omega) fun q hq1 hq2 => by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [M.alpha_involutive] at h
          have := hinj q (b' + 1) (by omega) (by omega) h
          omega
        · rw [M.alpha_involutive] at h
          have := hinj q (a + 1) (by omega) ham h
          omega
    rw [show c + (b' - c) = b' by omega] at hch
    rw [hfp]
    exact Relation.EqvGen.trans _ _ _ hch hcα
  · have hsig : (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).sigma (f (a + 1)) =
        M.facePerm (M.alpha (f b)) := by
      have h := JunctionPocket.joined_sigma_alpha_right (M := M) (M.alpha (f b)) (M.alpha (f (a + 1)))
      rwa [M.alpha_involutive (f (a + 1))] at h
    have hch := reach_chain hstep (p := M.alpha (f b)) (e := M.alpha (f (a + 1))) (a + 1)
      (c - (a + 1)) (by omega) fun q hq1 hq2 => by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [M.alpha_involutive] at h
          have := hinj q b (by omega) (by omega) h
          omega
        · rw [M.alpha_involutive] at h
          have := hinj q (a + 1) (by omega) ham h
          omega
    rw [show a + 1 + (c - (a + 1)) = c by omega] at hch
    refine Relation.EqvGen.trans _ (f (a + 1)) _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr hsig))) ?_
    refine Relation.EqvGen.trans _ (M.alpha (f (a + 1))) _
      (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hch) hcα

/-- **The pocket.**  At a junction `σ (α w[a]) = w[b]` with `b ≤ a < m - 1`, joining `α w[b]`
and `α w[a+1]` separates `w[a]` from every outer dart outside `[b, a]`. -/
theorem not_reach_outside (hM : M.IsPlanar) {f : ℕ → M.Dart} {m : ℕ} {O : M.Face}
    (hstep : ∀ q, q + 1 < m → M.sigma (f (q + 1)) = M.alpha (f q))
    (hinj : ∀ i j, i < m → j < m → f i = f j → i = j)
    (hout : ∀ q, q < m → M.faceOf (M.alpha (f q)) = O)
    {a b c : ℕ} (hba : b ≤ a) (ham : a + 1 < m) (hjun : M.sigma (M.alpha (f a)) = f b)
    (hcm : c < m) (hc : c < b ∨ a < c) :
    ¬ Relation.EqvGen (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).Adjacent
      (f a) (f c) := by
  intro hac
  have hpe : M.alpha (f b) ≠ M.alpha (f (a + 1)) := fun h => by
    have := hinj b (a + 1) (by omega) ham (M.alpha.injective h)
    omega
  have hface : M.faceOf (M.alpha (f b)) = M.faceOf (M.alpha (f (a + 1))) :=
    (hout b (by omega)).trans (hout (a + 1) ham).symm
  have hpinch : M.sigma.SameCycle (M.alpha (M.alpha (f b))) (M.alpha (M.alpha (f (a + 1)))) := by
    rw [M.alpha_involutive (f b), M.alpha_involutive (f (a + 1)), ← hjun, ← hstep a ham]
    exact (Equiv.Perm.SameCycle.rfl.apply_right.apply_right).symm
  have hA : Relation.EqvGen (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).Adjacent
      (M.facePerm (M.alpha (f (a + 1)))) (f a) := by
    have h : M.facePerm (M.alpha (f (a + 1))) = M.alpha (f a) := by
      show M.sigma (M.alpha (M.alpha (f (a + 1)))) = M.alpha (f a)
      rw [M.alpha_involutive (f (a + 1))]
      exact hstep a ham
    rw [h]
    exact Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive (f a)))
  have hB := reach_outside hstep hinj hba ham hcm hc
  exact JunctionPocket.not_reach hM hpe hface hpinch
    (Relation.EqvGen.trans _ _ _ hB
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hac) (Relation.EqvGen.symm _ _ hA)))

/-- **The cell link.**  Two darts of inner faces joined across one inner face stay together
after any join at two darts of `O`. -/
theorem reach_via_cell {O : M.Face} {p e x₁ x₂ y₁ y₂ : M.Dart}
    (hp : M.faceOf p = O) (he : M.faceOf e = O)
    (h₁ : M.faceOf x₁ = M.faceOf y₁) (h₁O : M.faceOf x₁ ≠ O)
    (h₂ : M.faceOf x₂ = M.faceOf y₂) (h₂O : M.faceOf x₂ ≠ O)
    (hc : M.faceOf (M.alpha y₁) = M.faceOf (M.alpha y₂)) (hcO : M.faceOf (M.alpha y₁) ≠ O) :
    Relation.EqvGen (FoldMap.joined M p e).Adjacent x₁ x₂ := by
  have hr : ∀ x z : M.Dart, M.faceOf x ≠ O → M.faceOf x = M.faceOf z →
      Relation.EqvGen (FoldMap.joined M p e).Adjacent x z := fun x z hx hxz =>
    JunctionPocket.joined_reach_of_faceOf_eq (by rw [hp]; exact hx) (by rw [he]; exact hx) hxz
  refine Relation.EqvGen.trans _ y₁ _ (hr _ _ h₁O h₁) ?_
  refine Relation.EqvGen.trans _ (M.alpha y₁) _ (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_
  refine Relation.EqvGen.trans _ (M.alpha y₂) _ (hr _ _ hcO hc) ?_
  refine Relation.EqvGen.trans _ y₂ _
    (Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive y₂))) ?_
  exact Relation.EqvGen.symm _ _ (hr _ _ h₂O h₂)

/-- **Linked junctions coincide.** -/
theorem index_eq (hM : M.IsPlanar) {f : ℕ → M.Dart} {m : ℕ} {O : M.Face}
    (hstep : ∀ q, q + 1 < m → M.sigma (f (q + 1)) = M.alpha (f q))
    (hinj : ∀ i j, i < m → j < m → f i = f j → i = j)
    (hout : ∀ q, q < m → M.faceOf (M.alpha (f q)) = O)
    {a b c d : ℕ} (hba : b ≤ a) (ham : a + 1 < m) (hjab : M.sigma (M.alpha (f a)) = f b)
    (hdc : d ≤ c) (hcm : c + 1 < m) (hjcd : M.sigma (M.alpha (f c)) = f d)
    (hcls : ∀ p e : M.Dart, M.faceOf p = O → M.faceOf e = O →
      Relation.EqvGen (FoldMap.joined M p e).Adjacent (f a) (f c)) : a = c := by
  have hca : c ≤ a := not_lt.1 fun hlt =>
    not_reach_outside hM hstep hinj hout hba ham hjab (by omega) (Or.inr hlt)
      (hcls _ _ (hout b (by omega)) (hout (a + 1) ham))
  have hac : a ≤ c := not_lt.1 fun hlt =>
    not_reach_outside hM hstep hinj hout hdc hcm hjcd (by omega) (Or.inr hlt)
      (Relation.EqvGen.symm _ _ (hcls _ _ (hout d (by omega)) (hout (c + 1) hcm)))
  exact Nat.le_antisymm hac hca

/-- A non-last dart of a list has a successor index. -/
theorem idx_succ_lt {α : Type*} [DecidableEq α] {w l : List α} {e : α} (hmem : e ∈ w)
    (he : e ∈ l.getLast?) (hnd : l.getLast? ≠ w.getLast?) : w.idxOf e + 1 < w.length := by
  have h := List.idxOf_lt_length_of_mem hmem
  by_contra hge
  apply hnd
  have heq : w.length - 1 = w.idxOf e := by omega
  rw [Option.mem_def.1 he, List.getLast?_eq_getElem?, heq, List.getElem?_eq_getElem h,
    List.getElem_idxOf h]

end Pocket

section Diagram

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The outer walk as a function of the index, with a default dart past its end. -/
noncomputable def outerAt (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (d₀ : S.diagram.toCombMap.Dart) (q : ℕ) : S.diagram.toCombMap.Dart :=
  if h : q < (outerDarts S.diagram).length then (outerDarts S.diagram)[q] else d₀

theorem outerAt_of_lt {d₀ : S.diagram.toCombMap.Dart} {q : ℕ}
    (h : q < (outerDarts S.diagram).length) : outerAt S d₀ q = (outerDarts S.diagram)[q] := by
  rw [outerAt, dif_pos h]

theorem outerDarts_isChain (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    (outerDarts S.diagram).IsChain fun x y =>
      S.diagram.toCombMap.sigma y = S.diagram.toCombMap.alpha x := by
  unfold outerDarts
  rw [List.isChain_map, List.isChain_reverse]
  exact (S.diagram.faceBoundary S.diagram.outerFace).chain.imp fun a b h => by
    show S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha a) =
      S.diagram.toCombMap.alpha (S.diagram.toCombMap.alpha b)
    rw [S.diagram.toCombMap.alpha_involutive b]
    exact h

theorem outerDarts_nodup (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    (outerDarts S.diagram).Nodup :=
  List.Nodup.map S.diagram.toCombMap.alpha.injective
    (List.nodup_reverse.2 (S.diagram.faceBoundary S.diagram.outerFace).nodup)

theorem faceOf_alpha_of_mem_outerDarts {x : S.diagram.toCombMap.Dart}
    (hx : x ∈ outerDarts S.diagram) :
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) = S.diagram.outerFace := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  rw [S.diagram.toCombMap.alpha_involutive y]
  exact ((S.diagram.faceBoundary S.diagram.outerFace).mem_iff y).1 (List.mem_reverse.1 hy)

theorem outerAt_step {d₀ : S.diagram.toCombMap.Dart} {q : ℕ}
    (hq : q + 1 < (outerDarts S.diagram).length) :
    S.diagram.toCombMap.sigma (outerAt S d₀ (q + 1)) =
      S.diagram.toCombMap.alpha (outerAt S d₀ q) := by
  rw [outerAt_of_lt hq, outerAt_of_lt (by omega : q < (outerDarts S.diagram).length)]
  exact List.isChain_iff_getElem.1 (outerDarts_isChain S) q hq

theorem outerAt_inj {d₀ : S.diagram.toCombMap.Dart} {i j : ℕ}
    (hi : i < (outerDarts S.diagram).length) (hj : j < (outerDarts S.diagram).length)
    (h : outerAt S d₀ i = outerAt S d₀ j) : i = j := by
  rw [outerAt_of_lt hi, outerAt_of_lt hj] at h
  exact (outerDarts_nodup S).getElem_inj_iff.1 h

theorem outerAt_idxOf {d₀ x : S.diagram.toCombMap.Dart} (hx : x ∈ outerDarts S.diagram) :
    outerAt S d₀ ((outerDarts S.diagram).idxOf x) = x := by
  rw [outerAt_of_lt (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]

/-- The first relator cell across polygon `k`, if any. -/
noncomputable def cellOf (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    Option (Fin S.diagram.rCellCount) :=
  if h : ∃ s < P.sideCount k, ∃ j, P.kind k s = .cell j then
    some (Classical.choose (Classical.choose_spec h).2)
  else none

theorem cellOf_isSome (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    (hk : k ∈ P.relatorPolygons) : ∃ j, cellOf P k = some j := by
  unfold cellOf
  rw [dif_pos (Finset.mem_filter.1 hk).2]
  exact ⟨_, rfl⟩

theorem cellOf_spec (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    {j : Fin S.diagram.rCellCount} (h : cellOf P k = some j) :
    ∃ y, S.diagram.toCombMap.faceOf y = P.face k ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) =
        (Embedded.cell S.diagram j).face := by
  unfold cellOf at h
  by_cases hex : ∃ s < P.sideCount k, ∃ j, P.kind k s = .cell j
  · rw [dif_pos hex, Option.some_inj] at h
    subst h
    have hs0 := (Classical.choose_spec hex).1
    have hj := Classical.choose_spec (Classical.choose_spec hex).2
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (P.side_ne_nil k _ hs0)
    exact ⟨y, P.faceOf_of_mem_sideDarts hs0 hy,
      ((S.diagram.faceBoundary (Embedded.cell S.diagram _).face).mem_iff _).1
        (P.alpha_mem_cellDarts_of_mem_cellSideDarts hs0 hj hy)⟩
  · rw [dif_neg hex] at h
    cases h

/-- The data of a backward junction on the outer walk. -/
theorem junction_data (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ}
    (hs : s ∈ P.backwardJunctions k) :
    s < P.sideCount k ∧ ∃ e e' : S.diagram.toCombMap.Dart,
      e ∈ (P.sideDarts k s).getLast? ∧ e ∈ outerDarts S.diagram ∧ e' ∈ outerDarts S.diagram ∧
        S.diagram.toCombMap.facePerm e = e' ∧
          (outerDarts S.diagram).idxOf e' ≤ (outerDarts S.diagram).idxOf e := by
  obtain ⟨hbad, hback⟩ := Finset.mem_filter.1 hs
  obtain ⟨hbad', j, hj⟩ := Finset.mem_filter.1 hbad
  obtain ⟨hsr, hjoin, _⟩ := Finset.mem_filter.1 hbad'
  have hsc : s < P.sideCount k := Finset.mem_range.1 hsr
  obtain ⟨e, he, e', he', hle⟩ := hback
  have hs' : (s + 1) % P.sideCount k < P.sideCount k := Nat.mod_lt _ (by omega)
  obtain ⟨_, arc, harc, _⟩ := P.boundary_arc k s j hsc hj
  obtain ⟨_, arc', harc', _⟩ := P.boundary_arc k ((s + 1) % P.sideCount k) j hs'
    (by rw [← hjoin.1]; exact hj)
  refine ⟨hsc, e, e', he, ?_, ?_, P.facePerm_getLast_eq_head_mod hsc he he', hle⟩
  · have hd : e ∈ arc.darts := by
      rw [← harc]
      exact List.mem_of_mem_getLast? he
    exact arc.mem_cycle_of_mem_darts hd
  · have hd : e' ∈ arc'.darts := by
      rw [← harc']
      exact List.mem_of_mem_head? he'
    exact arc'.mem_cycle_of_mem_darts hd

/-- The last dart of a side determines the polygon and the side. -/
theorem sigma_eq_of_getLast (P : OsinLemma94RealizedPolygons S)
    {x y : (_ : Fin P.count) × ℕ} (hx : x.2 < P.sideCount x.1) (hy : y.2 < P.sideCount y.1)
    {e : S.diagram.toCombMap.Dart} (hex : e ∈ (P.sideDarts x.1 x.2).getLast?)
    (hey : e ∈ (P.sideDarts y.1 y.2).getLast?) : x = y := by
  obtain ⟨k₁, s₁⟩ := x
  obtain ⟨k₂, s₂⟩ := y
  have hk : k₁ = k₂ := P.face_injective
    ((P.faceOf_of_mem_sideDarts hx (List.mem_of_mem_getLast? hex)).symm.trans
      (P.faceOf_of_mem_sideDarts hy (List.mem_of_mem_getLast? hey)))
  subst hk
  by_contra hne
  have hs : s₁ ≠ s₂ := fun h => hne (by rw [h])
  exact P.sideDarts_disjoint _ hx hy hs (List.mem_of_mem_getLast? hex)
    (List.mem_of_mem_getLast? hey)

/-- **Two non-degenerate backward junctions of polygons sharing a relator cell have the same
last dart.** -/
theorem getLast_eq_of_cell (P : OsinLemma94RealizedPolygons S) {k₁ k₂ : Fin P.count}
    {j : Fin S.diagram.rCellCount} (hj₁ : cellOf P k₁ = some j) (hj₂ : cellOf P k₂ = some j)
    {s₁ s₂ : ℕ} {e₁ e₁' e₂ e₂' : S.diagram.toCombMap.Dart}
    (hs₁ : s₁ < P.sideCount k₁) (he₁ : e₁ ∈ (P.sideDarts k₁ s₁).getLast?)
    (he₁w : e₁ ∈ outerDarts S.diagram) (he₁'w : e₁' ∈ outerDarts S.diagram)
    (hf₁ : S.diagram.toCombMap.facePerm e₁ = e₁')
    (hle₁ : (outerDarts S.diagram).idxOf e₁' ≤ (outerDarts S.diagram).idxOf e₁)
    (hnd₁ : (P.sideDarts k₁ s₁).getLast? ≠ (outerDarts S.diagram).getLast?)
    (hs₂ : s₂ < P.sideCount k₂) (he₂ : e₂ ∈ (P.sideDarts k₂ s₂).getLast?)
    (he₂w : e₂ ∈ outerDarts S.diagram) (he₂'w : e₂' ∈ outerDarts S.diagram)
    (hf₂ : S.diagram.toCombMap.facePerm e₂ = e₂')
    (hle₂ : (outerDarts S.diagram).idxOf e₂' ≤ (outerDarts S.diagram).idxOf e₂)
    (hnd₂ : (P.sideDarts k₂ s₂).getLast? ≠ (outerDarts S.diagram).getLast?) : e₁ = e₂ := by
  obtain ⟨d₀⟩ : Nonempty S.diagram.toCombMap.Dart := ⟨e₁⟩
  have hfa₁ : outerAt S d₀ ((outerDarts S.diagram).idxOf e₁) = e₁ := outerAt_idxOf he₁w
  have hfa₂ : outerAt S d₀ ((outerDarts S.diagram).idxOf e₂) = e₂ := outerAt_idxOf he₂w
  have hjun₁ : S.diagram.toCombMap.sigma
      (S.diagram.toCombMap.alpha (outerAt S d₀ ((outerDarts S.diagram).idxOf e₁))) =
        outerAt S d₀ ((outerDarts S.diagram).idxOf e₁') := by
    rw [hfa₁, outerAt_idxOf he₁'w]
    exact hf₁
  have hjun₂ : S.diagram.toCombMap.sigma
      (S.diagram.toCombMap.alpha (outerAt S d₀ ((outerDarts S.diagram).idxOf e₂))) =
        outerAt S d₀ ((outerDarts S.diagram).idxOf e₂') := by
    rw [hfa₂, outerAt_idxOf he₂'w]
    exact hf₂
  obtain ⟨y₁, hy₁, hay₁⟩ := cellOf_spec P hj₁
  obtain ⟨y₂, hy₂, hay₂⟩ := cellOf_spec P hj₂
  have hface₁ := P.faceOf_of_mem_sideDarts hs₁ (List.mem_of_mem_getLast? he₁)
  have hface₂ := P.faceOf_of_mem_sideDarts hs₂ (List.mem_of_mem_getLast? he₂)
  have hac := index_eq S.diagram.planar (f := outerAt S d₀) (O := S.diagram.outerFace)
    (fun q hq => outerAt_step hq) (fun i j hi hj h => outerAt_inj hi hj h)
    (fun q hq => by
      rw [outerAt_of_lt hq]
      exact faceOf_alpha_of_mem_outerDarts (List.getElem_mem hq))
    hle₁ (idx_succ_lt he₁w he₁ hnd₁) hjun₁ hle₂ (idx_succ_lt he₂w he₂ hnd₂) hjun₂
    (fun p e hp he => by
      rw [hfa₁, hfa₂]
      exact reach_via_cell hp he (hface₁.trans hy₁.symm)
        (by rw [hface₁]; exact P.face_ne_outer k₁) (hface₂.trans hy₂.symm)
        (by rw [hface₂]; exact P.face_ne_outer k₂) (hay₁.trans hay₂.symm)
        (by rw [hay₁]; exact (Embedded.cell S.diagram j).face_ne_outer))
  exact hfa₁.symm.trans ((congrArg (outerAt S d₀) hac).trans hfa₂)

/-- The label of a junction: `none` when its last dart ends the outer walk, else the first
relator cell of its polygon. -/
noncomputable def junctionLabel (P : OsinLemma94RealizedPolygons S)
    (x : (_ : Fin P.count) × ℕ) : Option (Fin S.diagram.rCellCount) :=
  if (P.sideDarts x.1 x.2).getLast? = (outerDarts S.diagram).getLast? then none
  else cellOf P x.1

theorem junctionLabel_injOn (P : OsinLemma94RealizedPolygons S) {T : Finset (Fin P.count)}
    (hT : T ⊆ P.relatorPolygons) :
    Set.InjOn (junctionLabel P)
      ((T.sigma fun k => P.backwardJunctions k : Finset ((_ : Fin P.count) × ℕ)) :
        Set ((_ : Fin P.count) × ℕ)) := by
  intro x hx y hy hxy
  obtain ⟨hxk, hxs⟩ := Finset.mem_sigma.1 (Finset.mem_coe.1 hx)
  obtain ⟨hyk, hys⟩ := Finset.mem_sigma.1 (Finset.mem_coe.1 hy)
  obtain ⟨hxsc, ex, ex', hex, hexw, hex'w, hfx, hlex⟩ := junction_data P hxs
  obtain ⟨hysc, ey, ey', hey, heyw, hey'w, hfy, hley⟩ := junction_data P hys
  obtain ⟨jx, hjx⟩ := cellOf_isSome P (hT hxk)
  obtain ⟨jy, hjy⟩ := cellOf_isSome P (hT hyk)
  unfold junctionLabel at hxy
  by_cases hdx : (P.sideDarts x.1 x.2).getLast? = (outerDarts S.diagram).getLast?
  · by_cases hdy : (P.sideDarts y.1 y.2).getLast? = (outerDarts S.diagram).getLast?
    · refine sigma_eq_of_getLast P hxsc hysc hex ?_
      rw [hdy, ← hdx]
      exact hex
    · rw [if_pos hdx, if_neg hdy, hjy] at hxy
      cases hxy
  · by_cases hdy : (P.sideDarts y.1 y.2).getLast? = (outerDarts S.diagram).getLast?
    · rw [if_neg hdx, if_pos hdy, hjx] at hxy
      cases hxy
    · rw [if_neg hdx, if_neg hdy, hjx, hjy] at hxy
      have hexy : ex = ey := getLast_eq_of_cell P hjx (hxy ▸ hjy) hxsc hex hexw hex'w hfx hlex
        hdx hysc hey heyw hey'w hfy hley hdy
      refine sigma_eq_of_getLast P hxsc hysc hex ?_
      rw [hexy]
      exact hey

/-- **The count.**  Over any set of relator polygons, the backward junctions number at most
`n + 1`. -/
theorem backward_count (P : OsinLemma94RealizedPolygons S) {T : Finset (Fin P.count)}
    (hT : T ⊆ P.relatorPolygons) :
    ∑ k ∈ T, (P.backwardJunctions k).card ≤ Delta.rCellCount + 1 := by
  rw [← Finset.card_sigma T fun k => P.backwardJunctions k]
  refine (Finset.card_le_card_of_injOn (junctionLabel P) (t := Finset.univ)
    (fun x _ => Finset.mem_coe.2 (Finset.mem_univ (junctionLabel P x)))
    (junctionLabel_injOn P hT)).trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin, S.equiv.rCellCount_eq]

end Diagram

/-- **Osin's Lemma 9.4, backward junctions.** -/
theorem proof : OsinLemma94BackwardJunctionCountInput.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨0, fun _ _ => ⟨1, Nat.one_pos, fun _ _ _ _ _ _ _ _ _ S _ _ P _ => ?_⟩⟩
  exact backward_count P (Finset.filter_subset _ _)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01BackwardJunctions

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01BackwardJunctions.proof
