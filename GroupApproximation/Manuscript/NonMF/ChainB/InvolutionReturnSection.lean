import GroupApproximation.Dynamics.TransientCells
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:involution-localization`, proof: the enlarged section and its classes

`non_mf_groups_exist.tex`, proof of Lemma `lem:involution-localization` (tex 1673–1686):

> Let $K\subset X\setminus Y$ contain the sources and ranges of a finite partial-shift description
> of $F$, and cover $K$ by $m$ wandering clopen sets.  Each orbit meets $K$ at most $m$ times.
> If $H$ bounds the return gaps, add arrows from every point of $K$ to its first $2m$ strictly
> future returns to $C$.  [...]  Each generated class contains an original point and its $2m$
> distinct return points.

Objects (nothing assumed beyond the printed setting):
* `C` has bounded positive return times: `hret : ∀ x, ∃ h, 0 < h ∧ h ≤ H ∧ T^h x ∈ C`;
* `K` is covered by `m` wandering sets `W i`;
* `returnTimes T C x t`: the return times of `x` to `C` in `[1, t]`;
* `firstReturns T C m N x`: the returns `h ≤ N` of `x` whose rank among the returns is at most
  `2m`, i.e. the first `2m` strictly future returns.  For `N = 2mH` it has exactly `2m`
  elements (`card_firstReturns`), so no return among the first `2m` is cut off by `N`;
* `arrowSection T K C m N`: the points of `K` together with the first `2m` returns of points of
  `K`, the endpoints of the added arrows; `arrowExponents N` their displacements `1, ..., N`.

The classes are those of the matrix-block construction of `lem:transient-matrices` in the corpus
(`ChainCore.reachableExponents` for the section `arrowSection` and the exponents
`E0 ∪ arrowExponents (2mH)`, where `E0` is any finite partial-shift description), saturated after
`M - 1` steps for the orbit bound `M = m (2mH + 1)` of the section (`exponentBound_arrowSection`).

Endpoint: `manuscriptSentence_classContainsOriginalAndReturnPoints` (tex 1681–1682).
-/

namespace GroupApproximation.Manuscript.NonMF.ChainB

open GroupApproximation.ChainCore

section ReturnSection

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (K C : Set X) (m N : ℕ)

open Classical in
/-- The return times of `x` to `C` in `[1, t]`. -/
noncomputable def returnTimes (x : X) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ C

theorem mem_returnTimes {x : X} {t h : ℕ} :
    h ∈ returnTimes T C x t ↔ (1 ≤ h ∧ h ≤ t) ∧ (T ^ (h : ℤ)) x ∈ C := by
  unfold returnTimes
  rw [Finset.mem_filter, Finset.mem_Icc]

theorem returnTimes_mono (x : X) {h t : ℕ} (hht : h ≤ t) :
    returnTimes T C x h ⊆ returnTimes T C x t := by
  intro h' hh'
  obtain ⟨⟨h1, h2⟩, hC'⟩ := (mem_returnTimes T C).1 hh'
  exact (mem_returnTimes T C).2 ⟨⟨h1, le_trans h2 hht⟩, hC'⟩

open Classical in
/-- **The first `2m` strictly future returns** of `x` to `C`, among the times `≤ N`: the returns
whose rank among the returns is at most `2m`. -/
noncomputable def firstReturns (x : X) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun h : ℕ => (T ^ (h : ℤ)) x ∈ C ∧ (returnTimes T C x h).card ≤ 2 * m

theorem mem_firstReturns {x : X} {h : ℕ} :
    h ∈ firstReturns T C m N x ↔
      (1 ≤ h ∧ h ≤ N) ∧ (T ^ (h : ℤ)) x ∈ C ∧ (returnTimes T C x h).card ≤ 2 * m := by
  unfold firstReturns
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- The endpoints of the added arrows: `K` and the first `2m` returns of its points. -/
def arrowSection : Set X :=
  K ∪ ⋃ h ∈ Finset.Icc 1 N, ⇑(T ^ (-(h : ℤ))) ⁻¹' (K ∩ {x | h ∈ firstReturns T C m N x})

/-- The displacements `1, ..., N` of the added arrows. -/
def arrowExponents : Finset ℤ :=
  (Finset.Icc 1 N).image (Nat.cast : ℕ → ℤ)

/-! ### Clopenness -/

theorem isLocallyConstant_firstReturns (hC : IsClopen C) :
    IsLocallyConstant (firstReturns T C m N) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  filter_upwards [(Filter.eventually_all_finset (Finset.Icc 1 N)).2 fun h _ =>
    eventually_zpow_mem_iff (T := T) hC (h : ℤ) x] with y hy
  have hinner : ∀ h ∈ Finset.Icc 1 N, returnTimes T C y h = returnTimes T C x h := fun h hh =>
    Finset.ext fun h' => by
      rw [mem_returnTimes, mem_returnTimes]
      exact and_congr_right fun hh' =>
        hy h' (Finset.mem_Icc.2 ⟨hh'.1, le_trans hh'.2 (Finset.mem_Icc.1 hh).2⟩)
  refine Finset.ext fun h => ?_
  rw [mem_firstReturns, mem_firstReturns]
  exact and_congr_right fun hh => by
    rw [hy h (Finset.mem_Icc.2 hh), hinner h (Finset.mem_Icc.2 hh)]

theorem isClopen_setOf_mem_firstReturns (hC : IsClopen C) (h : ℕ) :
    IsClopen {x : X | h ∈ firstReturns T C m N x} := by
  have hset : {x : X | h ∈ firstReturns T C m N x} =
      {x | ((fun S : Finset ℕ => h ∈ S) ∘ firstReturns T C m N) x = True} :=
    Set.ext fun _ => ⟨eq_true, of_eq_true⟩
  rw [hset]
  exact ((isLocallyConstant_firstReturns T C m N hC).comp fun S : Finset ℕ => h ∈ S).isClopen_fiber
    True

/-- **The enlarged section is clopen.** -/
theorem isClopen_arrowSection (hK : IsClopen K) (hC : IsClopen C) :
    IsClopen (arrowSection T K C m N) :=
  hK.union (isClopen_biUnion_finset fun h _ =>
    (hK.inter (isClopen_setOf_mem_firstReturns T C m N hC h)).preimage
      (T ^ (-(h : ℤ))).continuous)

theorem subset_arrowSection : K ⊆ arrowSection T K C m N :=
  Set.subset_union_left

theorem zpow_mem_arrowSection {x : X} {h : ℕ} (hx : x ∈ K) (hh : h ∈ firstReturns T C m N x) :
    (T ^ (h : ℤ)) x ∈ arrowSection T K C m N := by
  refine (Set.mem_union _ _ _).2 (Or.inr (Set.mem_iUnion₂.2
    ⟨h, Finset.mem_Icc.2 ((mem_firstReturns T C m N).1 hh).1, ?_⟩))
  show (T ^ (-(h : ℤ))) ((T ^ (h : ℤ)) x) ∈ K ∩ {x | h ∈ firstReturns T C m N x}
  rw [Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero, Homeomorph.one_apply]
  exact ⟨hx, hh⟩

/-! ### Counting the first returns -/

/-- A discrete intermediate value theorem for functions growing by at most one per step. -/
theorem exists_eq_of_le_succ (f : ℕ → ℕ) (h0 : f 0 = 0) (hstep : ∀ t, f (t + 1) ≤ f t + 1)
    (n : ℕ) : ∀ N : ℕ, n ≤ f N → ∃ t ≤ N, f t = n := by
  intro N
  induction N with
  | zero => intro hn; exact ⟨0, le_rfl, by omega⟩
  | succ N ih =>
    intro hn
    by_cases hN : n ≤ f N
    · obtain ⟨t, ht, hft⟩ := ih hN
      exact ⟨t, by omega, hft⟩
    · exact ⟨N + 1, le_rfl, by have := hstep N; omega⟩

/-- **A point has exactly `2m` first returns within `2mH`**, when `H` bounds the return gaps. -/
theorem card_firstReturns {H : ℕ} (hret : ∀ x, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C)
    (x : X) : (firstReturns T C m (2 * m * H) x).card = 2 * m := by
  have h0 : (returnTimes T C x 0).card = 0 :=
    Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun h hh => by
      obtain ⟨⟨h1, h2⟩, -⟩ := (mem_returnTimes T C).1 hh
      omega)
  have hstep : ∀ t, (returnTimes T C x (t + 1)).card ≤ (returnTimes T C x t).card + 1 := by
    intro t
    have hsub : returnTimes T C x (t + 1) ⊆ insert (t + 1) (returnTimes T C x t) := by
      intro h hh
      obtain ⟨⟨h1, h2⟩, hCh⟩ := (mem_returnTimes T C).1 hh
      rcases Nat.lt_or_ge h (t + 1) with hlt | hge
      · exact Finset.mem_insert_of_mem ((mem_returnTimes T C).2 ⟨⟨h1, by omega⟩, hCh⟩)
      · have hht : h = t + 1 := by omega
        rw [hht]
        exact Finset.mem_insert_self _ _
    exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
  obtain ⟨t, htN, hteq⟩ := exists_eq_of_le_succ (fun t => (returnTimes T C x t).card) h0 hstep
    (2 * m) (2 * m * H) (Dynamics.card_returns_ge T C H hret x (2 * m))
  have hteq' : (returnTimes T C x t).card = 2 * m := hteq
  have hlow : returnTimes T C x t ⊆ firstReturns T C m (2 * m * H) x := by
    intro h hh
    obtain ⟨⟨h1, h2⟩, hCh⟩ := (mem_returnTimes T C).1 hh
    exact (mem_firstReturns T C m _).2 ⟨⟨h1, le_trans h2 htN⟩, hCh,
      le_trans (Finset.card_le_card (returnTimes_mono T C x h2)) hteq'.le⟩
  have hmaps : Set.MapsTo (fun h => (returnTimes T C x h).card)
      (firstReturns T C m (2 * m * H) x : Set ℕ) (Finset.Icc 1 (2 * m) : Set ℕ) := by
    intro h hh
    obtain ⟨⟨h1, -⟩, hCh, hle⟩ := (mem_firstReturns T C m _).1 (Finset.mem_coe.1 hh)
    exact Finset.mem_coe.2 (Finset.mem_Icc.2
      ⟨Finset.card_pos.2 ⟨h, (mem_returnTimes T C).2 ⟨⟨h1, le_rfl⟩, hCh⟩⟩, hle⟩)
  have key : ∀ a b : ℕ, 1 ≤ b → (T ^ (b : ℤ)) x ∈ C → a < b →
      (returnTimes T C x a).card < (returnTimes T C x b).card := fun a b hb hbC hab =>
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
      ⟨returnTimes_mono T C x hab.le, fun heq' => by
        have hbm : b ∈ returnTimes T C x b := (mem_returnTimes T C).2 ⟨⟨hb, le_rfl⟩, hbC⟩
        rw [← heq'] at hbm
        obtain ⟨⟨-, hba⟩, -⟩ := (mem_returnTimes T C).1 hbm
        omega⟩)
  have hinj : Set.InjOn (fun h => (returnTimes T C x h).card)
      (firstReturns T C m (2 * m * H) x : Set ℕ) := by
    intro h hh h' hh' heq
    obtain ⟨⟨h1, -⟩, hCh, -⟩ := (mem_firstReturns T C m _).1 (Finset.mem_coe.1 hh)
    obtain ⟨⟨h1', -⟩, hCh', -⟩ := (mem_firstReturns T C m _).1 (Finset.mem_coe.1 hh')
    have heq2 : (returnTimes T C x h).card = (returnTimes T C x h').card := heq
    rcases lt_trichotomy h h' with hlt | heq3 | hgt
    · exact absurd heq2 (key h h' h1' hCh' hlt).ne
    · exact heq3
    · exact absurd heq2 (key h' h h1 hCh hgt).ne'
  refine le_antisymm ?_ ?_
  · calc (firstReturns T C m (2 * m * H) x).card ≤ (Finset.Icc 1 (2 * m)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = 2 * m := (Nat.card_Icc 1 (2 * m)).trans (by omega)
  · calc 2 * m = (returnTimes T C x t).card := hteq'.symm
      _ ≤ (firstReturns T C m (2 * m * H) x).card := Finset.card_le_card hlow

/-! ### The orbit bound for the enlarged section -/

/-- **Each orbit meets the enlarged section at most `m (N + 1)` times**: every point of the section
is `T^h` of a point of `K` for some `0 ≤ h ≤ N`, and each orbit meets `K` at most `m` times. -/
theorem exponentBound_arrowSection {W : Fin m → Set X}
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i) :
    ExponentBound T (arrowSection T K C m N) (m * (N + 1)) := by
  intro x S hS
  have hsel : ∀ n ∈ S, ∃ p : ℕ × ℕ, ∃ hp : p.1 < m, p.2 < N + 1 ∧
      (T ^ (n - (p.2 : ℤ))) x ∈ W ⟨p.1, hp⟩ := by
    intro n hn
    have hK' : ∃ h : ℕ, h < N + 1 ∧ (T ^ (n - (h : ℤ))) x ∈ K := by
      rcases (Set.mem_union _ _ _).1 (hS n hn) with hK | hU
      · exact ⟨0, Nat.succ_pos N, by rwa [Nat.cast_zero, sub_zero]⟩
      · obtain ⟨h, hh, hKh⟩ := Set.mem_iUnion₂.1 hU
        refine ⟨h, Nat.lt_succ_of_le (Finset.mem_Icc.1 hh).2, ?_⟩
        have hKh' : (T ^ (-(h : ℤ))) ((T ^ n) x) ∈ K := hKh.1
        rwa [Dynamics.zpow_apply_zpow_apply, neg_add_eq_sub] at hKh'
    obtain ⟨h, hlt, hKh⟩ := hK'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKW hKh)
    exact ⟨(i.1, h), i.2, hlt, hi⟩
  choose! ι hι using hsel
  have hinj : Set.InjOn ι (S : Set ℤ) := by
    intro n hn n' hn' heq
    obtain ⟨hlt1, -, h1⟩ := hι n hn
    obtain ⟨hlt1', -, h2⟩ := hι n' hn'
    have hfin : (⟨(ι n).1, hlt1⟩ : Fin m) = ⟨(ι n').1, hlt1'⟩ := Fin.ext (congrArg Prod.fst heq)
    rw [hfin] at h1
    have hmem : (T ^ ((n - ((ι n).2 : ℤ)) - (n' - ((ι n').2 : ℤ))))
        ((T ^ (n' - ((ι n').2 : ℤ))) x) ∈ W ⟨(ι n').1, hlt1'⟩ := by
      rwa [Dynamics.zpow_apply_zpow_apply, sub_add_cancel]
    have hd := Dynamics.eq_zero_of_isWandering T (hWw _) h2 hmem
    have h2eq : (ι n).2 = (ι n').2 := congrArg Prod.snd heq
    omega
  calc S.card ≤ (Finset.range m ×ˢ Finset.range (N + 1)).card :=
        Finset.card_le_card_of_injOn ι (fun n hn => Finset.mem_coe.2 (Finset.mem_product.2
          ⟨Finset.mem_range.2 (hι n hn).1, Finset.mem_range.2 (hι n hn).2.1⟩)) hinj
    _ = m * (N + 1) := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-! ### Classes of the enlarged section -/

/-- Every class meets `K`: a point of the section is an original point or a first return of one,
reached back by one inverse arrow. -/
theorem exists_origin_mem_class {E : Finset ℤ} (hE : arrowExponents N ⊆ E) {Mb : ℕ}
    (hbound : ExponentBound T (arrowSection T K C m N) Mb) {y : X}
    (hy : y ∈ arrowSection T K C m N) :
    ∃ d ∈ reachableExponents T (arrowSection T K C m N) E (Mb - 1) y, (T ^ d) y ∈ K := by
  rcases (Set.mem_union _ _ _).1 hy with hK | hU
  · refine ⟨0, zero_mem_reachableExponents hy, ?_⟩
    rwa [zpow_zero, Homeomorph.one_apply]
  · obtain ⟨h, hh, hKh⟩ := Set.mem_iUnion₂.1 hU
    have hKh' : (T ^ (-(h : ℤ))) y ∈ K := hKh.1
    have hEh : (h : ℤ) ∈ E := hE (Finset.mem_image.2 ⟨h, hh, rfl⟩)
    have h1 : -(h : ℤ) ∈ reachableExponents T (arrowSection T K C m N) E (0 + 1) y :=
      mem_reachableExponents_succ.2 ⟨Or.inr ⟨0, zero_mem_reachableExponents hy, -(h : ℤ),
        neg_mem_stepExponents (mem_stepExponents.2 (Or.inl hEh)), zero_add _⟩,
        (Set.mem_union _ _ _).2 (Or.inl hKh')⟩
    refine ⟨-(h : ℤ), ?_, hKh'⟩
    rw [← reachableExponents_eq_of_le (E := E) hbound y (r := Mb - 1 + 1) (by omega)]
    exact reachableExponents_mono (by omega) y h1

/-- The first returns of an original point of a class lie in the class: one arrow each. -/
theorem add_mem_class_of_return {E : Finset ℤ} (hE : arrowExponents N ⊆ E) {Mb : ℕ}
    (hbound : ExponentBound T (arrowSection T K C m N) Mb) {y : X} {d : ℤ}
    (hd : d ∈ reachableExponents T (arrowSection T K C m N) E (Mb - 1) y) (hdK : (T ^ d) y ∈ K)
    {h : ℕ} (hh : h ∈ firstReturns T C m N ((T ^ d) y)) :
    (h : ℤ) + d ∈ reachableExponents T (arrowSection T K C m N) E (Mb - 1) y := by
  have hEh : (h : ℤ) ∈ E :=
    hE (Finset.mem_image.2 ⟨h, Finset.mem_Icc.2 ((mem_firstReturns T C m N).1 hh).1, rfl⟩)
  have hstep : (h : ℤ) ∈ reachableExponents T (arrowSection T K C m N) E (0 + 1) ((T ^ d) y) :=
    mem_reachableExponents_succ.2 ⟨Or.inr ⟨0, zero_mem_reachableExponents
      ((Set.mem_union _ _ _).2 (Or.inl hdK)), (h : ℤ), mem_stepExponents.2 (Or.inl hEh),
      zero_add _⟩, zpow_mem_arrowSection T K C m N hdK hh⟩
  have hadd := add_mem_reachableExponents hd (0 + 1) hstep
  rwa [reachableExponents_eq_of_le (E := E) hbound y (r := 0 + 1 + (Mb - 1)) (by omega)] at hadd

/-- A nonzero power moves every point of `K`. -/
theorem zpow_ne_self_of_mem {W : Fin m → Set X}
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i) {x : X} (hx : x ∈ K)
    {h : ℤ} (hh : h ≠ 0) : (T ^ h) x ≠ x := by
  intro heq
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKW hx)
  have hmem : (T ^ h) x ∈ W i := by rw [heq]; exact hi
  exact hh (Dynamics.eq_zero_of_isWandering T (hWw i) hi hmem)

/-- Distinct powers send a point of `K` to distinct points. -/
theorem eq_of_zpow_eq_of_mem {W : Fin m → Set X}
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i) {x : X} (hx : x ∈ K)
    {h h' : ℤ} (heq : (T ^ h) x = (T ^ h') x) : h = h' := by
  by_contra hne
  exact zpow_ne_self_of_mem T K m hWw hKW hx (by omega) (Dynamics.zpow_sub_apply_of_eq T heq)

end ReturnSection

/-- **"Each generated class contains an original point and its $2m$ distinct return points"**
(tex 1681–1682).  Let `C` have positive return times bounded by `H`, let `K` be covered by `m`
wandering sets, and generate classes from the section `arrowSection T K C m (2mH)` (the points of
`K` and the endpoints of the arrows to their first `2m` strictly future returns) and any finite
partial-shift description `E0` together with the arrow displacements.  Every class (the class of
any point `y` of the section, saturated after `M - 1` steps, `M = m (2mH + 1)`) contains an
original point `T^d y ∈ K` and its first `2m` returns: there are exactly `2m` of them, each lies
in the class, differs from the original point, and distinct returns give distinct points. -/
theorem manuscriptSentence_classContainsOriginalAndReturnPoints
    {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (K C : Set X) (m H : ℕ) {W : Fin m → Set X}
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i)
    (hret : ∀ x, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) (E0 : Finset ℤ) :
    ∀ y ∈ arrowSection T K C m (2 * m * H),
      ∃ d ∈ reachableExponents T (arrowSection T K C m (2 * m * H))
          (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) y,
        (T ^ d) y ∈ K ∧
        (firstReturns T C m (2 * m * H) ((T ^ d) y)).card = 2 * m ∧
        (∀ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) y),
          (h : ℤ) + d ∈ reachableExponents T (arrowSection T K C m (2 * m * H))
            (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) y ∧
          (T ^ ((h : ℤ) + d)) y ≠ (T ^ d) y) ∧
        ∀ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) y),
          ∀ h' ∈ firstReturns T C m (2 * m * H) ((T ^ d) y),
            (T ^ ((h : ℤ) + d)) y = (T ^ ((h' : ℤ) + d)) y → h = h' := by
  intro y hy
  have hbound := exponentBound_arrowSection T K C m (2 * m * H) hWw hKW
  obtain ⟨d, hd, hdK⟩ :=
    exists_origin_mem_class T K C m (2 * m * H) Finset.subset_union_right hbound hy
  refine ⟨d, hd, hdK, card_firstReturns T C m hret _, fun h hh =>
    ⟨add_mem_class_of_return T K C m _ Finset.subset_union_right hbound hd hdK hh, ?_⟩,
    fun h hh h' _ heq => ?_⟩
  · rw [← Dynamics.zpow_apply_zpow_apply]
    refine zpow_ne_self_of_mem T K m hWw hKW hdK ?_
    have h1 := ((mem_firstReturns T C m _).1 hh).1.1
    omega
  · rw [← Dynamics.zpow_apply_zpow_apply, ← Dynamics.zpow_apply_zpow_apply] at heq
    exact_mod_cast eq_of_zpow_eq_of_mem T K m hWw hKW hdK heq

end GroupApproximation.Manuscript.NonMF.ChainB

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainB.manuscriptSentence_classContainsOriginalAndReturnPoints
