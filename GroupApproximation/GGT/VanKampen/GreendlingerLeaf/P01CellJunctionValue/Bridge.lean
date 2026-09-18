import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Region
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingChains
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PendantRemoval
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionExclusion
import GroupApproximation.Meta.AxiomGuard

/-!
# Case B: every side of the polygon is an arc of `C`

Inside a hole region every dart of the polygon face `f` has across it `f` or `C` (`region_fact`).
A dart `d` with `f` on both sides is impossible (`no_selfEdge`): with `L` least such that
`facePerm^(L + 1) d = α d`, the face walk `A_d = facePerm d, …, facePerm^L d` closes past `α d`;
`L = 0` is a leaf (against `DartMinimal`), and by strong induction on `L` some dart of `A_d` has `C`
across it, so `C` is enclosed by `A_d`.  The same holds for `α d`, and the dart of `A_{α d}` with
`C` across lies on `A_d` (else `f` is enclosed by `A_d`); the minimality of both lengths refutes
this.

Hence no side is a cutting path, and every side is of kind `cell j` (`kind_eq_cell`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

open Equiv GroupApproximation.GGT.VanKampen.Embedded SimpleClosedWalkSides FirstTurnEnclosure
open scoped Classical

universe u w v

/-- Cancellation of powers. -/
theorem pow_cancel {α : Type*} {p : Perm α} {x y : α} {i j : ℕ} (hij : i ≤ j)
    (h : (p ^ j) y = (p ^ i) x) : (p ^ (j - i)) y = x := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  rw [Nat.add_sub_cancel_left]
  apply (p ^ i).injective
  rw [← h, pow_add, Perm.mul_apply]

/-- Two rotation steps from the reversal, past a dart off the edges of `c`, are a first turn. -/
theorem firstTurn_two {M : CombMap.{v}} {c : List M.Dart} {x y z : M.Dart}
    (h₁ : M.sigma (M.alpha x) = z) (h₂ : M.sigma z = y) (hz : ¬ walkKeep M c z) :
    FirstTurn M c x y := by
  refine ⟨2, by omega, ?_, fun t ht htk => ?_⟩
  · rw [pow_two, Perm.mul_apply, h₁, h₂]
  · obtain rfl : t = 1 := by omega
    rw [pow_one, h₁]
    exact hz

section Self

variable {M : CombMap.{v}}

/-- The least return of a dart with the same face on both sides. -/
theorem exists_least_return {d : M.Dart} (hd : M.faceOf (M.alpha d) = M.faceOf d) :
    ∃ L, (M.facePerm ^ (L + 1)) d = M.alpha d ∧
      ∀ t < L, (M.facePerm ^ (t + 1)) d ≠ M.alpha d := by
  obtain ⟨n, hn⟩ := ((M.faceOf_eq_iff d (M.alpha d)).mp hd.symm).exists_nat_pow_eq
  have hex : ∃ L, (M.facePerm ^ (L + 1)) d = M.alpha d := by
    rcases n with _ | n
    · rw [pow_zero, Perm.one_apply] at hn
      exact (M.alpha_fixedPointFree d hn.symm).elim
    · exact ⟨n, hn⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun t ht => Nat.find_min hex ht⟩

variable {d : M.Dart} {L : ℕ}

/-- Before its least return, the face walk of `d` does not come back to `d`. -/
theorem pow_ne_self (hL : (M.facePerm ^ (L + 1)) d = M.alpha d)
    (hleast : ∀ t < L, (M.facePerm ^ (t + 1)) d ≠ M.alpha d) :
    ∀ i, 0 < i → i ≤ L → (M.facePerm ^ i) d ≠ d := by
  intro i hi hiL h
  apply hleast (L - i) (by omega)
  rw [← pow_add_apply_of_fix h (L - i + 1), show L - i + 1 + i = L + 1 by omega]
  exact hL

theorem selfSeg_nodup (hL : (M.facePerm ^ (L + 1)) d = M.alpha d)
    (hleast : ∀ t < L, (M.facePerm ^ (t + 1)) d ≠ M.alpha d) :
    (seg M (M.facePerm d) L).Nodup := by
  refine seg_nodup fun r hr0 hrL h => pow_ne_self hL hleast r hr0 hrL.le ?_
  apply M.facePerm.injective
  rw [← pow_succ_apply, pow_succ_apply']
  exact h

theorem alpha_not_mem_selfSeg (hleast : ∀ t < L, (M.facePerm ^ (t + 1)) d ≠ M.alpha d) :
    M.alpha d ∉ seg M (M.facePerm d) L := by
  intro h
  obtain ⟨r, hr, hreq⟩ := mem_seg.mp h
  rw [← pow_succ_apply'] at hreq
  exact hleast r hr hreq

theorem not_mem_selfSeg (hL : (M.facePerm ^ (L + 1)) d = M.alpha d)
    (hleast : ∀ t < L, (M.facePerm ^ (t + 1)) d ≠ M.alpha d) :
    d ∉ seg M (M.facePerm d) L := by
  intro h
  obtain ⟨r, hr, hreq⟩ := mem_seg.mp h
  rw [← pow_succ_apply'] at hreq
  exact pow_ne_self hL hleast (r + 1) (by omega) (by omega) hreq

/-- **The self walk closes** past `α d`. -/
theorem selfSeg_firstTurn (hL0 : L ≠ 0) (hL : (M.facePerm ^ (L + 1)) d = M.alpha d)
    (hleast : ∀ t < L, (M.facePerm ^ (t + 1)) d ≠ M.alpha d) :
    FirstTurn M (seg M (M.facePerm d) L) ((seg M (M.facePerm d) L).getLast (seg_ne_nil hL0))
      ((seg M (M.facePerm d) L).head (seg_ne_nil hL0)) := by
  rw [seg_getLast hL0, seg_head hL0]
  have h₁ : M.sigma (M.alpha ((M.facePerm ^ (L - 1)) (M.facePerm d))) = M.alpha d := by
    show M.facePerm ((M.facePerm ^ (L - 1)) (M.facePerm d)) = M.alpha d
    rw [← pow_succ_apply, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hL0),
      ← pow_succ_apply']
    exact hL
  refine firstTurn_two h₁ rfl ?_
  rintro (h | h)
  · exact alpha_not_mem_selfSeg hleast h
  · rw [M.alpha_involutive d] at h
    exact not_mem_selfSeg hL hleast h

variable {f C : M.Face}

/-- **Some dart of the self walk has `C` across.** -/
theorem exists_cross_of_return (hM : M.IsPlanar) (_hfC : f ≠ C)
    (hacross : ∀ y, M.faceOf y = f → M.faceOf (M.alpha y) = f ∨ M.faceOf (M.alpha y) = C)
    (hnoleaf : ∀ d, M.faceOf d = f → M.facePerm d ≠ M.alpha d) :
    ∀ (L : ℕ) (d : M.Dart), M.faceOf d = f → (M.facePerm ^ (L + 1)) d = M.alpha d →
      (∀ t < L, (M.facePerm ^ (t + 1)) d ≠ M.alpha d) →
      ∃ y ∈ seg M (M.facePerm d) L, M.faceOf (M.alpha y) = C := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro d hd hL hleast
    have hL0 : L ≠ 0 := by
      rintro rfl
      rw [zero_add, pow_one] at hL
      exact hnoleaf d hd hL
    have hc : seg M (M.facePerm d) L ≠ [] := seg_ne_nil hL0
    have hclose := selfSeg_firstTurn hL0 hL hleast
    have hx : M.facePerm d ∈ seg M (M.facePerm d) L :=
      mem_seg.mpr ⟨0, Nat.pos_of_ne_zero hL0, by rw [pow_zero, Perm.one_apply]⟩
    have hxf : M.faceOf (M.facePerm d) = f := (M.faceOf_facePerm d).trans hd
    rcases hacross _ hxf with hxα | hxα
    · have hmem := (mem_iff_of_chain hM hc (seg_isChain _ _) hclose (M.facePerm d)).mp hx
      have hαx : M.alpha (M.facePerm d) ∈ seg M (M.facePerm d) L := by
        rcases hmem.2 with h | h
        · rw [hxα, ← hxf] at h
          exact (hmem.1 h).elim
        · exact h
      obtain ⟨r, hrL, hr⟩ := mem_seg.mp hαx
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [pow_zero, Perm.one_apply] at hr
        exact M.alpha_fixedPointFree _ hr.symm
      obtain ⟨Lx, hLx, hLxleast⟩ :=
        exists_least_return (M := M) (d := M.facePerm d) (hxα.trans hxf.symm)
      have hLxr : Lx + 1 ≤ r := by
        by_contra hlt
        apply hLxleast (r - 1) (by omega)
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr0)]
        exact hr
      obtain ⟨y, hy, hyC⟩ := ih Lx (by omega) (M.facePerm d) hxf hLx hLxleast
      exact ⟨y, seg_facePerm_subset (by omega) hy, hyC⟩
    · exact ⟨M.facePerm d, hx, hxα⟩

/-- **No dart has the face `f` on both sides.** -/
theorem no_selfEdge (hM : M.IsPlanar) (hfC : f ≠ C)
    (hacross : ∀ y, M.faceOf y = f → M.faceOf (M.alpha y) = f ∨ M.faceOf (M.alpha y) = C)
    (hnoleaf : ∀ d, M.faceOf d = f → M.facePerm d ≠ M.alpha d)
    {d : M.Dart} (hd : M.faceOf d = f) (hαd : M.faceOf (M.alpha d) = f) : False := by
  obtain ⟨L, hL, hleast⟩ := exists_least_return (M := M) (d := d) (hαd.trans hd.symm)
  have hα' : M.faceOf (M.alpha (M.alpha d)) = M.faceOf (M.alpha d) := by
    rw [M.alpha_involutive d, hd, hαd]
  obtain ⟨L', hL', hleast'⟩ := exists_least_return (M := M) (d := M.alpha d) hα'
  have hL0 : L ≠ 0 := by
    rintro rfl
    rw [zero_add, pow_one] at hL
    exact hnoleaf d hd hL
  obtain ⟨y₁, hy₁, hy₁C⟩ := exists_cross_of_return hM hfC hacross hnoleaf L d hd hL hleast
  obtain ⟨y₂, hy₂, hy₂C⟩ :=
    exists_cross_of_return hM hfC hacross hnoleaf L' (M.alpha d) hαd hL' hleast'
  have hc : seg M (M.facePerm d) L ≠ [] := seg_ne_nil hL0
  have hclose := selfSeg_firstTurn hL0 hL hleast
  have hx : M.facePerm d ∈ seg M (M.facePerm d) L :=
    mem_seg.mpr ⟨0, Nat.pos_of_ne_zero hL0, by rw [pow_zero, Perm.one_apply]⟩
  have hsegf : ∀ z ∈ seg M (M.facePerm d) L, M.faceOf z = f := fun z hz =>
    (faceOf_of_mem_seg hz).trans ((M.faceOf_facePerm d).trans hd)
  -- `C` is enclosed by the self walk of `d`.
  have hCE : C ∈ enclosedFaces M (seg M (M.facePerm d) L) := by
    have hmem := (mem_iff_of_chain hM hc (seg_isChain _ _) hclose y₁).mp hy₁
    rcases hmem.2 with h | h
    · rwa [hy₁C] at h
    · exact (hfC ((hsegf _ h).symm.trans hy₁C)).elim
  -- The dart of the self walk of `α d` with `C` across lies on the self walk of `d`.
  have hy₂mem : y₂ ∈ seg M (M.facePerm d) L := by
    by_contra hy₂not
    have hk : ¬ walkKeep M (seg M (M.facePerm d) L) (M.alpha y₂) := by
      rintro (h | h)
      · exact hfC ((hsegf _ h).symm.trans hy₂C)
      · rw [M.alpha_involutive y₂] at h
        exact hy₂not h
    have hy₂f : M.faceOf y₂ = M.faceOf (M.facePerm d) := by
      rw [faceOf_of_mem_seg hy₂, M.faceOf_facePerm, M.faceOf_facePerm, hαd, hd]
    have hfE := faceOf_alpha_mem_enclosedFaces hk (by rw [hy₂C]; exact hCE)
    rw [M.alpha_involutive y₂, hy₂f] at hfE
    exact faceOf_not_mem_of_chain hM hc (seg_isChain _ _) hclose hx hfE
  obtain ⟨r, hrL, hr⟩ := mem_seg.mp hy₂mem
  obtain ⟨r', hr'L, hr'⟩ := mem_seg.mp hy₂
  rw [← pow_succ_apply'] at hr hr'
  rcases le_or_gt r r' with hrr | hrr
  · have h := pow_cancel (show r + 1 ≤ r' + 1 by omega) (hr'.trans hr.symm)
    rcases Nat.eq_zero_or_pos (r' - r) with h0 | h0
    · rw [show r' + 1 - (r + 1) = 0 by omega, pow_zero, Perm.one_apply] at h
      exact M.alpha_fixedPointFree d h
    · apply hleast' (r' - r - 1) (by omega)
      rw [show r' - r - 1 + 1 = r' + 1 - (r + 1) by omega, M.alpha_involutive d]
      exact h
  · have h := pow_cancel (show r' + 1 ≤ r + 1 by omega) (hr.trans hr'.symm)
    apply hleast (r - r' - 1) (by omega)
    rw [show r - r' - 1 + 1 = r + 1 - (r' + 1) by omega]
    exact h

end Self

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **Inside a hole region the polygon face is on one side of each edge only.** -/
theorem no_selfEdge_face (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hmin : S.DartMinimal) (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    {j : Fin S.diagram.rCellCount} {E : Finset S.diagram.toCombMap.Face}
    (hH : HoleRegion S.diagram (P.face k) (cell S.diagram j).face E)
    {d : S.diagram.toCombMap.Dart} (hd : S.diagram.toCombMap.faceOf d = P.face k)
    (hαd : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) = P.face k) : False := by
  have hf : S.UnselectedGFace (P.face k) :=
    ⟨P.face_ne_outer k, fun C' hC' h => hH.2.2.2.1 C' hC' (by rw [h]; exact hH.1),
      P.face_unselected k⟩
  exact no_selfEdge S.diagram.planar (fun h => P.face_not_cell k j h.symm)
    (fun y hy => region_fact hvalue P hH hy)
    (fun d' hd' hleaf => GloballyDistinguishedSectionFamily.not_leaf_of_dartMinimal
      GloballyDistinguishedSectionFamily.pendantPathRemovalInput hmin hf hd' hleaf) hd hαd

/-- **Every side of the polygon is an arc of `C`.** -/
theorem kind_eq_cell (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hmin : S.DartMinimal) (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    {j : Fin S.diagram.rCellCount} {E : Finset S.diagram.toCombMap.Face}
    (hH : HoleRegion S.diagram (P.face k) (cell S.diagram j).face E)
    {i : ℕ} (hi : i < P.sideCount k) : P.kind k i = .cell j := by
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (P.side_ne_nil k i hi)
  have hyf : S.diagram.toCombMap.faceOf y = P.face k := P.faceOf_of_mem_sideDarts hi hy
  rcases sideClass_cases (P.kind k i) with ⟨j', hj'⟩ | ⟨j', hj'⟩ | hcut | hshort
  · have hαcell := P.alpha_mem_cellDarts_of_mem_cellSideDarts hi hj' hy
    have hαf : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) =
        (cell S.diagram j').face := faceOf_of_mem_cellDarts hαcell
    rcases region_fact hvalue P hH hyf with h | h
    · exact (P.face_not_cell k j' (hαf.symm.trans h)).elim
    · rw [hj', cell_face_injective S.diagram (hαf.symm.trans h)]
  · obtain ⟨_, arc, harc, _⟩ := P.boundary_arc k i j' hi hj'
    rw [harc] at hy
    have hout : y ∈ outerDarts S.diagram := arc.mem_cycle_of_mem_darts hy
    simp only [outerDarts, List.mem_map, List.mem_reverse] at hout
    obtain ⟨e, he, rfl⟩ := hout
    have he' : S.diagram.toCombMap.faceOf e = S.diagram.outerFace :=
      ((S.diagram.faceBoundary S.diagram.outerFace).mem_iff e).mp he
    rcases region_fact hvalue P hH hyf with h | h
    · rw [S.diagram.toCombMap.alpha_involutive e, he'] at h
      exact (P.face_ne_outer k h.symm).elim
    · rw [S.diagram.toCombMap.alpha_involutive e, he'] at h
      exact ((cell S.diagram j).face_ne_outer h.symm).elim
  · exact (no_selfEdge_face hvalue hmin P hH hyf (P.cutting_internal k i hi hcut y hy)).elim
  · obtain ⟨a, ha, hsa⟩ := P.short_region k i hi hshort
    have hmemα := hsa y hy
    rcases region_fact hvalue P hH hyf with h | h
    · rw [h] at hmemα
      exact (P.face_unselected k a ha hmemα).elim
    · rw [h] at hmemα
      exact (CellHairThickening.relatorFace_not_mem hvalue (cell_mem S.diagram j) a hmemα).elim

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue
