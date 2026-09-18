import GroupApproximation.Manuscript.NonMF.Full.InvolutionBlocks.BlockCells
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:involution-localization`, proof: the placement read off the representative cells

`non_mf_groups_exist.tex`, proof of `\label{lem:involution-localization}`, tex 1678–1686:

> Apply the finite matrix-block construction of Lemma~\ref{lem:transient-matrices}, refining also
> by $K$ and $C$.  Each generated class contains an original point and its $2m$ distinct return
> points.  At least $m$ of the latter lie in $C\setminus K$, enough to match every original
> coordinate to a fresh section coordinate.  Swap the matched pairs and fix the other coordinates.
> The finite clopen partition makes these choices constant on each representative cell.

`exists_blockPlacement_of_transientCells` produces the data of the swaps as a
`Dynamics.IsPlacement` (`Dynamics/ReturnPlacement`): with the refined cells `cell a` and matchings
`σ a` of `exists_blockMatching`, the cell `A j h` of the `j`-th cover piece of `K` with exponent `h`
is the union, over the cells `a` and the original coordinates `d ∈ S a` matched to `h + d`, of the
levels `T^d (cell a ∩ T^{-d}(piece j))`.  The fields of the placement come from the printed
argument:

* the cells are clopen and cover `K`, because every point of `K` is a level of a representative
  (`ChainCore.exists_mem_baseCell_level`) and the cells cover the representatives;
* different exponents give disjoint cells, and different cells or coordinates give disjoint fresh
  coordinates, because representatives and exponents are unique
  (`ChainCore.eq_of_zpow_eq_of_mem_baseSet`) and the matching is injective;
* the fresh coordinates `T^h (A j h)` lie in `C ∖ K` because the matched coordinates do.
-/

namespace GroupApproximation.Full.NM19

open GroupApproximation.ChainCore

/-- **The matrix-block placement** (`lem:involution-localization`, proof, tex 1678–1686).  Let `X`
be compact, `K`, `C` and the wandering sets `W i` clopen, `K ⊆ ⋃ i, W i`, `C` with positive return
times bounded by `H`, and `E0` a finite partial-shift description.  The refined representative
cells `cell a` (inside the base cells of the section `arrowSection T K C m (2mH)` for the exponents
`E0 ∪ arrowExponents (2mH)`) with their matchings `σ a` give a placement `A` of all `m` pieces, whose
cells are, explicitly, the levels of the representative cells at the matched original
coordinates. -/
theorem exists_blockPlacement_of_transientCells
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (T : X ≃ₜ X) {K C : Set X}
    (hK : IsClopen K) (hC : IsClopen C) (m H : ℕ) {W : Fin m → Set X} (hW : ∀ i, IsClopen (W i))
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i)
    (hret : ∀ x, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) (E0 : Finset ℤ) :
    ∃ (M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ) (σ : Fin M → ℤ → ℤ)
      (A : Fin m → ℕ → Set X),
      (∀ a, IsClopen (cell a)) ∧
      (∀ a, cell a ⊆ baseCell T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1)) (S a)) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧
      (∀ a, ∀ y ∈ cell a, ∀ d ∈ S a, (T ^ d) y ∈ K →
        σ a d ∈ S a ∧ (T ^ (σ a d)) y ∈ C ∧ (T ^ (σ a d)) y ∉ K ∧
          ∃ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) y), σ a d = (h : ℤ) + d) ∧
      (∀ j h, A j h = ⋃ a, ⋃ d ∈ (S a).filter (fun d => σ a d = (h : ℤ) + d),
        ⇑(T ^ d) '' (cell a ∩ ⇑(T ^ d) ⁻¹' Dynamics.coverPiece W K j)) ∧
      Dynamics.IsPlacement T W K C H m A := by
  obtain ⟨M, cell, S, σ, hcl, hsub, hdisj, -, hcov, hσ1, hσinj⟩ :=
    exists_blockMatching T hK hC m H hWw hKW hret E0
  have hbound := exponentBound_arrowSection T K C m (2 * m * H) hWw hKW
  obtain ⟨A, hA⟩ : ∃ A : Fin m → ℕ → Set X, ∀ j h,
      A j h = ⋃ a, ⋃ d ∈ (S a).filter (fun d => σ a d = (h : ℤ) + d),
        ⇑(T ^ d) '' (cell a ∩ ⇑(T ^ d) ⁻¹' Dynamics.coverPiece W K j) :=
    ⟨fun j h => ⋃ a, ⋃ d ∈ (S a).filter (fun d => σ a d = (h : ℤ) + d),
      ⇑(T ^ d) '' (cell a ∩ ⇑(T ^ d) ⁻¹' Dynamics.coverPiece W K j), fun _ _ => rfl⟩
  have hmemA : ∀ j h x, x ∈ A j h ↔ ∃ a : Fin M, ∃ d ∈ S a, σ a d = (h : ℤ) + d ∧
      ∃ y ∈ cell a, (T ^ d) y ∈ Dynamics.coverPiece W K j ∧ (T ^ d) y = x := by
    intro j h x
    rw [hA]
    constructor
    · intro hx
      obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hx
      obtain ⟨d, hdF, hxd⟩ := Set.mem_iUnion₂.1 hxa
      obtain ⟨y, ⟨hy, hyP⟩, hyx⟩ := hxd
      obtain ⟨hdS, hσ⟩ := Finset.mem_filter.1 hdF
      exact ⟨a, d, hdS, hσ, y, hy, hyP, hyx⟩
    · rintro ⟨a, d, hdS, hσ, y, hy, hyP, hyx⟩
      exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion₂.2 ⟨d, Finset.mem_filter.2 ⟨hdS, hσ⟩,
        ⟨y, ⟨hy, hyP⟩, hyx⟩⟩⟩
  have hR : ∀ a, ∀ y ∈ cell a, reachableExponents T (arrowSection T K C m (2 * m * H))
      (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) y = S a :=
    fun a y hy => (hsub a hy).2
  have hbase : ∀ a, ∀ y ∈ cell a, y ∈ baseSet T (arrowSection T K C m (2 * m * H))
      (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1)) :=
    fun a y hy => (hsub a hy).1
  have hcellEq : ∀ a a', ∀ y ∈ cell a, ∀ y' ∈ cell a', y = y' → a = a' := by
    intro a a' y hy y' hy' hyy
    by_contra hne
    rw [hyy] at hy
    exact Set.disjoint_left.1 (hdisj a a' hne) hy hy'
  refine ⟨M, cell, S, σ, A, hcl, hsub, hdisj, hσ1, hA, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- isClopen
    intro j h
    rw [hA]
    exact isClopen_iUnion_of_finite fun a => isClopen_biUnion_finset fun d _ =>
      Dynamics.isClopen_zpow_image T d ((hcl a).inter
        ((Dynamics.isClopen_coverPiece W K hK hW j).preimage (T ^ d).continuous))
  · -- subset
    intro j h x hx
    obtain ⟨a, d, -, -, y, -, hyP, hyx⟩ := (hmemA j h x).1 hx
    rw [← hyx]
    exact hyP
  · -- bounds
    rintro j h ⟨x, hx⟩
    obtain ⟨a, d, hdS, hσ, y, hy, hyP, -⟩ := (hmemA j h x).1 hx
    have hdK : (T ^ d) y ∈ K := (Dynamics.coverPiece_subset W K j hyP).1
    obtain ⟨-, -, -, h', hfr, hσ'⟩ := hσ1 a y hy d hdS hdK
    have hhh : h = h' := by omega
    obtain ⟨⟨h1, h2⟩, -⟩ := (mem_firstReturns T C m _).1 hfr
    rw [hhh]
    exact ⟨j.2, by omega, h2⟩
  · -- cover
    intro j _ x hx
    have hxK : x ∈ K := (Dynamics.coverPiece_subset W K j hx).1
    obtain ⟨x0, d, hx0, hd, hdx⟩ := exists_mem_baseCell_level (E := E0 ∪ arrowExponents (2 * m * H))
      hbound (subset_arrowSection T K C m (2 * m * H) hxK)
    obtain ⟨a, hxa⟩ := hcov x0 hx0.1
    have hdS : d ∈ S a := by
      rw [← hR a x0 hxa]
      exact hd
    have hdK : (T ^ d) x0 ∈ K := by
      rw [hdx]
      exact hxK
    obtain ⟨-, -, -, h, -, hσ⟩ := hσ1 a x0 hxa d hdS hdK
    refine ⟨h, (hmemA j h x).2 ⟨a, d, hdS, hσ, x0, hxa, ?_, hdx⟩⟩
    rw [hdx]
    exact hx
  · -- disjoint_same
    intro j h h' hne
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨a, d, hdS, hσ, y, hy, -, hyx⟩ := (hmemA j h x).1 hx
    obtain ⟨a', d', hdS', hσ', y', hy', -, hyx'⟩ := (hmemA j h' x).1 hx'
    have hdR : d ∈ reachableExponents T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) y := by
      rw [hR a y hy]
      exact hdS
    have hdR' : d' ∈ reachableExponents T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) y' := by
      rw [hR a' y' hy']
      exact hdS'
    obtain ⟨hyy, hdd⟩ := eq_of_zpow_eq_of_mem_baseSet hbound (hbase a y hy) (hbase a' y' hy')
      hdR hdR' (hyx.trans hyx'.symm)
    have haa : a = a' := hcellEq a a' y hy y' hy' hyy
    subst haa
    subst hdd
    exact hne (by omega)
  · -- target
    intro j h z hz
    obtain ⟨x, hx, hxz⟩ := hz
    obtain ⟨a, d, hdS, hσ, y, hy, hyP, hyx⟩ := (hmemA j h x).1 hx
    have hdK : (T ^ d) y ∈ K := (Dynamics.coverPiece_subset W K j hyP).1
    obtain ⟨-, hσC, hσK, -⟩ := hσ1 a y hy d hdS hdK
    rw [← hxz, ← hyx, Dynamics.zpow_apply_zpow_apply, ← hσ]
    exact ⟨hσC, hσK⟩
  · -- disjoint_target
    intro j h j' h' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨x, hx, hxz⟩ := hz
    obtain ⟨x', hx', hxz'⟩ := hz'
    obtain ⟨a, d, hdS, hσ, y, hy, hyP, hyx⟩ := (hmemA j h x).1 hx
    obtain ⟨a', d', hdS', hσ', y', hy', hyP', hyx'⟩ := (hmemA j' h' x').1 hx'
    have hdK : (T ^ d) y ∈ K := (Dynamics.coverPiece_subset W K j hyP).1
    have hdK' : (T ^ d') y' ∈ K := (Dynamics.coverPiece_subset W K j' hyP').1
    obtain ⟨hσS, -, -, -⟩ := hσ1 a y hy d hdS hdK
    obtain ⟨hσS', -, -, -⟩ := hσ1 a' y' hy' d' hdS' hdK'
    have hσR : σ a d ∈ reachableExponents T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) y := by
      rw [hR a y hy]
      exact hσS
    have hσR' : σ a' d' ∈ reachableExponents T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) y' := by
      rw [hR a' y' hy']
      exact hσS'
    have heq : (T ^ (σ a d)) y = (T ^ (σ a' d')) y' := by
      rw [hσ, hσ', ← Dynamics.zpow_apply_zpow_apply, ← Dynamics.zpow_apply_zpow_apply, hyx, hyx',
        hxz, hxz']
    obtain ⟨hyy, hdd⟩ := eq_of_zpow_eq_of_mem_baseSet hbound (hbase a y hy) (hbase a' y' hy')
      hσR hσR' heq
    have haa : a = a' := hcellEq a a' y hy y' hy' hyy
    subst haa
    subst hyy
    have hdd' : d = d' := hσinj a y hy d hdS d' hdS' hdK hdK' hdd
    subst hdd'
    have hjj : j = j' := by
      by_contra hne'
      exact Set.disjoint_left.1 (Dynamics.disjoint_coverPiece W K hne') hyP hyP'
    subst hjj
    have hhh : h = h' := by omega
    exact hne (by rw [hhh])

end GroupApproximation.Full.NM19

#audit_axioms GroupApproximation.Full.NM19.exists_blockPlacement_of_transientCells
