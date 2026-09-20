import GroupApproximation.Manuscript.NonMF.Full.InvolutionBlocks.BlockCells
import GroupApproximation.Manuscript.NonMF.Full.AtomRepresentatives.AtomCells
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:involution-localization`, proof: the matrix-block construction over first-atom representatives

`non_mf_groups_exist.tex`, proof of `\label{lem:involution-localization}`, tex 1678–1686:

> Apply the finite matrix-block construction of Lemma~\ref{lem:transient-matrices}, refining also
> by $K$ and $C$.  Each generated class contains an original point and its $2m$ distinct return
> points.  At least $m$ of the latter lie in $C\setminus K$, enough to match every original
> coordinate to a fresh section coordinate.  Swap the matched pairs and fix the other coordinates.
> The finite clopen partition makes these choices constant on each representative cell.

`Full.NM19` (`InvolutionBlocks/BlockCells`) refines the cells of `ClopenCrossedProduct.exists_cells`,
whose representatives are the points of least exponent in their class.  The matrix-block
construction of `lem:transient-matrices` as printed (tex 1510–1517) uses a separating clopen
partition and the representative in the first occupied atom (`AtomRepresentatives`).  This module
applies that construction to the section of the added arrows:

* `exists_blockCells_atoms`: over clopen atoms of a clopen section `L`, the first-atom representative
  set refined by the class exponents, the occupied atoms, and membership of `T^(d+j) y` in `K` and in
  `C` for every class exponent `d` and `0 ≤ j ≤ N`;
* `manuscriptSentence_matrixBlockConstructionRefinedByKC` (tex 1678–1680): for the section
  `L = arrowSection T K C m (2mH)` and the exponents `E0 ∪ arrowExponents (2mH)`, separating atoms of
  `L` exist and the atom cells can be refined also by `K` and `C`;
* `manuscriptSentence_choicesConstantOnRepresentativeCells` (tex 1682–1686): on each such cell a
  matching `σ a` of the original coordinates to fresh coordinates `h + d ∈ C ∖ K`, `h` a first
  return, the same on the whole cell and injective.

The sentence of tex 1681–1682 (each generated class contains an original point and its `2m`
distinct return points) is `NM19.generatedClasses_card`, which does not depend on the choice of
representatives.
-/

namespace GroupApproximation.Full.NMRegradeA

open GroupApproximation.ChainCore
open GroupApproximation.Full.NM19

/-- **The atom cells, refined also by `K` and `C`**: over clopen atoms of a clopen section `L`, the
first-atom representative set splits into finitely many pairwise disjoint nonempty clopen cells, on
which the class exponents, the occupied atoms at every class exponent, and membership of
`T^(d+j) y` in `K` and in `C` (`d` a class exponent, `0 ≤ j ≤ N`) do not depend on `y`. -/
theorem exists_blockCells_atoms {X : Type*} [TopologicalSpace X] [CompactSpace X] (T : X ≃ₜ X)
    {K C L : Set X} (hK : IsClopen K) (hC : IsClopen C) (hL : IsClopen L) (E : Finset ℤ)
    (Mb N : ℕ) {Na : ℕ} {atom : Fin Na → Set X} (hatom : ∀ i, IsClopen (atom i)) :
    ∃ (M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ),
      (∀ a, IsClopen (cell a)) ∧ (∀ a, cell a ⊆ atomBaseSet T L E Mb Na atom) ∧
      (∀ a, ∀ y ∈ cell a, reachableExponents T L E (Mb - 1) y = S a) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧ (∀ a, (cell a).Nonempty) ∧
      (∀ y ∈ atomBaseSet T L E Mb Na atom, ∃ a, y ∈ cell a) ∧
      (∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ d ∈ S a, ∀ i,
        ((T ^ d) y ∈ atom i ↔ (T ^ d) y' ∈ atom i)) ∧
      ∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ d ∈ S a, ∀ j : ℕ, j ≤ N →
        ((T ^ (d + (j : ℤ))) y ∈ K ↔ (T ^ (d + (j : ℤ))) y' ∈ K) ∧
          ((T ^ (d + (j : ℤ))) y ∈ C ↔ (T ^ (d + (j : ℤ))) y' ∈ C) := by
  classical
  obtain ⟨D, hD⟩ :=
    GroupApproximation.ClopenCrossedProduct.exists_finset_classExponents (T := T) (E := E)
      (m := Mb) hL
  obtain ⟨M, cell, S, hcl, hsub, hS, hdisj, hne, hcov, hocc, hconst⟩ :=
    exists_atomCells (T := T) (E := E) (m := Mb) hL hatom D
      (ι := {d // d ∈ D} × Fin (N + 1))
      (fun (p : {d // d ∈ D} × Fin (N + 1)) (y : X) =>
        ((T ^ ((p.1 : ℤ) + ((p.2 : ℕ) : ℤ))) y ∈ K, (T ^ ((p.1 : ℤ) + ((p.2 : ℕ) : ℤ))) y ∈ C))
      fun p => (isLocallyConstant_zpow_mem (T := T) hK ((p.1 : ℤ) + ((p.2 : ℕ) : ℤ))).prodMk
        (isLocallyConstant_zpow_mem (T := T) hC ((p.1 : ℤ) + ((p.2 : ℕ) : ℤ)))
  have hDS : ∀ a, ∀ y ∈ cell a, ∀ d ∈ S a, d ∈ D := fun a y hy d hd =>
    hD y (by rw [hS a y hy]; exact hd)
  refine ⟨M, cell, S, hcl, hsub, hS, hdisj, hne, hcov,
    fun a y hy y' hy' d hd i => hocc a y hy y' hy' d (hDS a y hy d hd) i,
    fun a y hy y' hy' d hd j hj => ?_⟩
  have hpair := hconst a y hy y' hy' (⟨d, hDS a y hy d hd⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
  exact ⟨Iff.of_eq (congrArg Prod.fst hpair), Iff.of_eq (congrArg Prod.snd hpair)⟩

/-- **"Apply the finite matrix-block construction of Lemma~\ref{lem:transient-matrices}, refining
also by $K$ and $C$"** (tex 1678–1680).  For the section `L = arrowSection T K C m (2mH)` of the
added arrows and the exponents `E0 ∪ arrowExponents (2mH)`, with the orbit bound `m (2mH + 1)`:
a separating clopen partition of `L` (tex 1510–1512), and cells of the first-atom representative
set (tex 1512–1517) refined also by membership in `K` and in `C` along each class. -/
theorem manuscriptSentence_matrixBlockConstructionRefinedByKC
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [TotallySeparatedSpace X] (T : X ≃ₜ X)
    {K C : Set X} (hK : IsClopen K) (hC : IsClopen C) (m H : ℕ) {W : Fin m → Set X}
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i) (E0 : Finset ℤ) :
    ∃ (Na : ℕ) (atom : Fin Na → Set X),
      IsSeparatingAtoms T (arrowSection T K C m (2 * m * H)) (E0 ∪ arrowExponents (2 * m * H))
        (m * (2 * m * H + 1)) Na atom ∧
      ∃ (M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ),
        (∀ a, IsClopen (cell a)) ∧
        (∀ a, cell a ⊆ atomBaseSet T (arrowSection T K C m (2 * m * H))
          (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1)) Na atom) ∧
        (∀ a, ∀ y ∈ cell a, reachableExponents T (arrowSection T K C m (2 * m * H))
          (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) y = S a) ∧
        (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧ (∀ a, (cell a).Nonempty) ∧
        (∀ y ∈ atomBaseSet T (arrowSection T K C m (2 * m * H))
          (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1)) Na atom, ∃ a, y ∈ cell a) ∧
        (∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ d ∈ S a, ∀ i,
          ((T ^ d) y ∈ atom i ↔ (T ^ d) y' ∈ atom i)) ∧
        ∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ d ∈ S a, ∀ j : ℕ, j ≤ 2 * m * H →
          ((T ^ (d + (j : ℤ))) y ∈ K ↔ (T ^ (d + (j : ℤ))) y' ∈ K) ∧
            ((T ^ (d + (j : ℤ))) y ∈ C ↔ (T ^ (d + (j : ℤ))) y' ∈ C) := by
  have hL := isClopen_arrowSection T K C m (2 * m * H) hK hC
  have hbound := exponentBound_arrowSection T K C m (2 * m * H) hWw hKW
  obtain ⟨Na, atom, hatoms⟩ := exists_separating_atoms hL hbound (E0 ∪ arrowExponents (2 * m * H))
  exact ⟨Na, atom, hatoms, exists_blockCells_atoms T hK hC hL (E0 ∪ arrowExponents (2 * m * H))
    (m * (2 * m * H + 1)) (2 * m * H) hatoms.isClopen⟩

/-- **"At least $m$ of the latter lie in $C\setminus K$, enough to match every original coordinate
to a fresh section coordinate [...]  The finite clopen partition makes these choices constant on
each representative cell"** (tex 1682–1686), over the first-atom representatives of the printed
matrix-block construction: on each refined cell `cell a` a matching `σ a`, depending only on the
cell, sends every original coordinate `d ∈ S a` (`T^d y ∈ K`) to a coordinate `σ a d = h + d ∈ S a`
of the class with `T^(σ a d) y ∈ C ∖ K`, `h` a first return of `T^d y`, and distinct original
coordinates to distinct fresh coordinates. -/
theorem manuscriptSentence_choicesConstantOnRepresentativeCells
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [TotallySeparatedSpace X] (T : X ≃ₜ X)
    {K C : Set X} (hK : IsClopen K) (hC : IsClopen C) (m H : ℕ) {W : Fin m → Set X}
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i)
    (hret : ∀ x, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) (E0 : Finset ℤ) :
    ∃ (Na : ℕ) (atom : Fin Na → Set X),
      IsSeparatingAtoms T (arrowSection T K C m (2 * m * H)) (E0 ∪ arrowExponents (2 * m * H))
        (m * (2 * m * H + 1)) Na atom ∧
      ∃ (M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ) (σ : Fin M → ℤ → ℤ),
        (∀ a, IsClopen (cell a)) ∧
        (∀ a, cell a ⊆ atomBaseSet T (arrowSection T K C m (2 * m * H))
          (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1)) Na atom) ∧
        (∀ a, ∀ y ∈ cell a, reachableExponents T (arrowSection T K C m (2 * m * H))
          (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) y = S a) ∧
        (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧ (∀ a, (cell a).Nonempty) ∧
        (∀ y ∈ atomBaseSet T (arrowSection T K C m (2 * m * H))
          (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1)) Na atom, ∃ a, y ∈ cell a) ∧
        (∀ a, ∀ y ∈ cell a, ∀ d ∈ S a, (T ^ d) y ∈ K →
          σ a d ∈ S a ∧ (T ^ (σ a d)) y ∈ C ∧ (T ^ (σ a d)) y ∉ K ∧
            ∃ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) y), σ a d = (h : ℤ) + d) ∧
        ∀ a, ∀ y ∈ cell a, ∀ d ∈ S a, ∀ d' ∈ S a, (T ^ d) y ∈ K → (T ^ d') y ∈ K →
          σ a d = σ a d' → d = d' := by
  classical
  obtain ⟨Na, atom, hatoms, M, cell, S, hcl, hsub, hSa, hdisj, hne, hcov, -, hconst⟩ :=
    manuscriptSentence_matrixBlockConstructionRefinedByKC T hK hC m H hWw hKW E0
  have hbound := exponentBound_arrowSection T K C m (2 * m * H) hWw hKW
  obtain ⟨y0, hy0⟩ : ∃ y0 : Fin M → X, ∀ a, y0 a ∈ cell a :=
    ⟨fun a => (hne a).some, fun a => (hne a).some_mem⟩
  have hK0 : ∀ a, ∀ y ∈ cell a, ∀ d ∈ S a, (T ^ d) y ∈ K → (T ^ d) (y0 a) ∈ K := by
    intro a y hy d hd hdK
    have h0 := (hconst a y hy (y0 a) (hy0 a) d hd 0 (Nat.zero_le _)).1
    rw [Nat.cast_zero, add_zero] at h0
    exact h0.1 hdK
  have hmatch : ∀ a : Fin M, ∃ σa : ℤ → ℤ,
      (∀ d ∈ (S a).filter (fun d => (T ^ d) (y0 a) ∈ K), σa d ∈ (S a).filter (fun e =>
        (T ^ e) (y0 a) ∈ C ∧ (T ^ e) (y0 a) ∉ K ∧
          ∃ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) (y0 a)), e = (h : ℤ) + d)) ∧
      Set.InjOn σa (((S a).filter (fun d => (T ^ d) (y0 a) ∈ K) : Finset ℤ) : Set ℤ) := by
    intro a
    have hS : reachableExponents T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) (y0 a) = S a :=
      hSa a (y0 a) (hy0 a)
    refine exists_injOn_of_card_le m (fun d : ℤ => (S a).filter fun e : ℤ =>
        (T ^ e) (y0 a) ∈ C ∧ (T ^ e) (y0 a) ∉ K ∧
          ∃ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) (y0 a)), e = (h : ℤ) + d)
      ((S a).filter fun d => (T ^ d) (y0 a) ∈ K)
      (exponentBound_of_wanderingCover (T := T) hWw hKW (y0 a)
        ((S a).filter fun d => (T ^ d) (y0 a) ∈ K) fun _ hd => (Finset.mem_filter.1 hd).2) ?_
    intro d hd
    obtain ⟨hdS, hdK⟩ := Finset.mem_filter.1 hd
    have hdreach : d ∈ reachableExponents T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) (y0 a) := by
      rw [hS]
      exact hdS
    have h1 : ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).card +
        ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => ¬ (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).card = 2 * m :=
      (Finset.card_filter_add_card_filter_not _).trans (card_firstReturns T C m hret _)
    have h2 : ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).card ≤ m :=
      Dynamics.card_visits_le T W K hWw hKW _ _
    have himg : ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => ¬ (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).image (fun h : ℕ => (h : ℤ) + d) ⊆
        (S a).filter fun e => (T ^ e) (y0 a) ∈ C ∧ (T ^ e) (y0 a) ∉ K ∧
          ∃ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) (y0 a)), e = (h : ℤ) + d := by
      intro e he
      obtain ⟨h, hh, hhe⟩ := Finset.mem_image.1 he
      have hhe' : (h : ℤ) + d = e := hhe
      obtain ⟨hfr, hnK⟩ := Finset.mem_filter.1 hh
      have hCh := ((mem_firstReturns T C m _).1 hfr).2.1
      rw [Dynamics.zpow_apply_zpow_apply, hhe'] at hCh hnK
      refine Finset.mem_filter.2 ⟨?_, hCh, hnK, h, hfr, hhe'.symm⟩
      rw [← hS, ← hhe']
      exact add_mem_class_of_return T K C m _ Finset.subset_union_right hbound hdreach hdK hfr
    have hinj : Function.Injective fun h : ℕ => (h : ℤ) + d := fun h h' heq => by
      have heq' : (h : ℤ) + d = (h' : ℤ) + d := heq
      have h3 : (h : ℤ) = h' := add_right_cancel heq'
      exact_mod_cast h3
    calc m ≤ ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => ¬ (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).card := by omega
      _ = (((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => ¬ (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).image
            (fun h : ℕ => (h : ℤ) + d)).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ _ := Finset.card_le_card himg
  choose σ hσR hσinj using hmatch
  refine ⟨Na, atom, hatoms, M, cell, S, σ, hcl, hsub, hSa, hdisj, hne, hcov,
    fun a y hy d hd hdK => ?_, fun a y hy d hd d' hd' hdK hdK' heq => ?_⟩
  · obtain ⟨hσS, hσC, hσK, h, hfr, hσeq⟩ :=
      Finset.mem_filter.1 (hσR a d (Finset.mem_filter.2 ⟨hd, hK0 a y hy d hd hdK⟩))
    have hwin := hconst a y hy (y0 a) (hy0 a) d hd h ((mem_firstReturns T C m _).1 hfr).1.2
    rw [hσeq, add_comm] at hσC hσK
    have hfrEq : firstReturns T C m (2 * m * H) ((T ^ d) y) =
        firstReturns T C m (2 * m * H) ((T ^ d) (y0 a)) :=
      firstReturns_congr T C m (2 * m * H) fun j _ hjN => by
        rw [Dynamics.zpow_apply_zpow_apply, Dynamics.zpow_apply_zpow_apply, add_comm]
        exact (hconst a y hy (y0 a) (hy0 a) d hd j hjN).2
    refine ⟨hσS, ?_, ?_, h, by rw [hfrEq]; exact hfr, hσeq⟩
    · rw [hσeq, add_comm]
      exact hwin.2.2 hσC
    · rw [hσeq, add_comm]
      exact fun hK' => hσK (hwin.1.1 hK')
  · exact hσinj a (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hd, hK0 a y hy d hd hdK⟩))
      (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hd', hK0 a y hy d' hd' hdK'⟩)) heq

end GroupApproximation.Full.NMRegradeA

#audit_axioms GroupApproximation.Full.NMRegradeA.exists_blockCells_atoms
#audit_axioms GroupApproximation.Full.NMRegradeA.manuscriptSentence_matrixBlockConstructionRefinedByKC
#audit_axioms GroupApproximation.Full.NMRegradeA.manuscriptSentence_choicesConstantOnRepresentativeCells
