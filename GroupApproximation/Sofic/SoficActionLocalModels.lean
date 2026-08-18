import GroupApproximation.Sofic.SoficActionOrbits

/-!
# Local subgroup and orbit models for sofic actions

Two local forms of permanence are useful when the subgroup used to model an
action is allowed to depend on both the tested group window and the tested site
window.

* `isSoficAction_of_local_subgroup_models` is the window-wise version of
  `isSoficAction_of_subgroup_cover`: one does not need the whole restricted
  action of the chosen subgroup to be sofic, only a model for the current
  window.
* `exists_model_of_window_stabilizers` is the finite-window version of
  `isSoficAction_of_stabilizers`: only the point stabilizers of sites actually
  appearing in the tested window are needed.

Both proofs are literal localizations of the corresponding global arguments in
`SoficAction` and `SoficActionOrbits`.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G] {X : Type u} [MulAction G X]

/-- A finite set of ambient elements, regarded as a finite set in a subgroup
which contains it. -/
noncomputable def finsetToSubgroup (F : Finset G) (K : Subgroup G)
    (hFK : ∀ g ∈ F, g ∈ K) : Finset K :=
  F.attach.image (fun p => (⟨p.1, hFK p.1 p.2⟩ : K))

@[simp] theorem mem_finsetToSubgroup (F : Finset G) (K : Subgroup G)
    (hFK : ∀ g ∈ F, g ∈ K) (g : G) (hg : g ∈ F) :
    (⟨g, hFK g hg⟩ : K) ∈ finsetToSubgroup F K hFK := by
  classical
  rw [finsetToSubgroup]
  exact Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨g, hg⟩)

/-- **Window-local subgroup lifting.**  To prove an ambient action sofic it is
enough, for every finite window, to place the tested group elements in a
subgroup and produce a sofic-action model for that one restricted window.  The
subgroup itself may depend on the site window and tolerance. -/
theorem isSoficAction_of_local_subgroup_models
    (h : ∀ (F : Finset G) (E : Finset X) (ε : ℝ), 0 < ε →
      ∃ (K : Subgroup G) (hFK : ∀ g ∈ F, g ∈ K),
        Nonempty (SoficActionModel K X (finsetToSubgroup F K hFK) E ε)) :
    IsSoficAction G X := by
  classical
  intro F E ε hε
  obtain ⟨K, hFK, hM⟩ := h F E ε hε
  obtain ⟨M⟩ := hM
  have hmemF' : ∀ g (hg : g ∈ F),
      (⟨g, hFK g hg⟩ : K) ∈ finsetToSubgroup F K hFK := by
    intro g hg
    exact mem_finsetToSubgroup F K hFK g hg
  exact ⟨{
    Site := M.Site
    siteFintype := M.siteFintype
    siteDecEq := M.siteDecEq
    siteNonempty := M.siteNonempty
    act := fun g => if hg : g ∈ K then M.act ⟨g, hg⟩ else 1
    act_one := by
      rw [dif_pos K.one_mem]
      have hone : (⟨(1 : G), K.one_mem⟩ : K) = 1 := rfl
      rw [hone]
      exact M.act_one
    act_mul := by
      intro g hg h hh
      have hgK : g ∈ K := hFK g hg
      have hhK : h ∈ K := hFK h hh
      rw [dif_pos hgK, dif_pos hhK, dif_pos (K.mul_mem hgK hhK)]
      have hsplit : (⟨g * h, K.mul_mem hgK hhK⟩ : K) =
          ⟨g, hgK⟩ * ⟨h, hhK⟩ := rfl
      rw [hsplit]
      exact M.act_mul _ (hmemF' g hg) _ (hmemF' h hh)
    good := M.good
    good_card := M.good_card
    Chart := M.Chart
    chartFintype := M.chartFintype
    chart := M.chart
    chart_inj := M.chart_inj
    chart_equivariant := by
      intro g hg s hs hgs x hx hgx
      have hgK : g ∈ K := hFK g hg
      rw [dif_pos hgK] at hgs ⊢
      exact M.chart_equivariant ⟨g, hgK⟩ (hmemF' g hg) s hs hgs x hx hgx }⟩

/-! ## Finite-window orbit gluing -/

/-- Local form of `exists_equivariant_cover_of_list`: only the coset actions
for points actually occurring in the list are assumed sofic. -/
theorem exists_equivariant_cover_of_list_of_mem
    (l : List X)
    (hst : ∀ x ∈ l, IsSoficAction G (G ⧸ MulAction.stabilizer G x)) :
    ∃ (Y : Type u) (_ : MulAction G Y) (f : Y → X),
      (∀ (g : G) (y : Y), f (g • y) = g • f y) ∧ Function.Injective f ∧
      (∀ x ∈ l, ∃ y, f y = x) ∧ IsSoficAction G Y := by
  classical
  revert hst
  induction l with
  | nil =>
      intro hst
      letI instE : MulAction G PEmpty.{u + 1} :=
        { smul := fun _ y => y.elim
          one_smul := fun y => y.elim
          mul_smul := fun _ _ y => y.elim }
      refine ⟨PEmpty.{u + 1}, instE, fun y => y.elim, ?_, ?_, ?_, ?_⟩
      · intro g y
        exact y.elim
      · intro y
        exact y.elim
      · intro x hx
        exact absurd hx (by simp)
      · exact isSoficAction_of_isEmpty
  | cons x l ih =>
      intro hst
      have hstl : ∀ z ∈ l, IsSoficAction G (G ⧸ MulAction.stabilizer G z) :=
        fun z hz => hst z (List.mem_cons_of_mem x hz)
      obtain ⟨Y, instY, f, hequiv, hinj, hmem, hY⟩ := ih hstl
      letI : MulAction G Y := instY
      by_cases hx : ∃ y, f y = x
      · refine ⟨Y, instY, f, hequiv, hinj, ?_, hY⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hx
        · exact hmem z hz'
      · letI : DecidableEq X := Classical.decEq _
        letI : DecidableEq Y := Classical.decEq _
        letI : DecidableEq (G ⧸ MulAction.stabilizer G x) := Classical.decEq _
        refine ⟨(G ⧸ MulAction.stabilizer G x) ⊕ Y, inferInstance,
          Sum.elim (orbitMap x) f, ?_, ?_, ?_, ?_⟩
        · intro g y
          cases y with
          | inl q => exact orbitMap_equivariant x g q
          | inr y => exact hequiv g y
        · intro y₁ y₂ hxy
          have hdisj : ∀ (q : G ⧸ MulAction.stabilizer G x) (y : Y),
              orbitMap x q ≠ f y := by
            intro q y hcon
            induction q using QuotientGroup.induction_on with
            | _ a =>
              apply hx
              refine ⟨a⁻¹ • y, ?_⟩
              rw [hequiv, ← hcon, orbitMap_mk, inv_smul_smul]
          cases y₁ with
          | inl q₁ =>
            cases y₂ with
            | inl q₂ =>
              exact congrArg Sum.inl (orbitMap_injective x hxy)
            | inr y₂ => exact absurd hxy (hdisj q₁ y₂)
          | inr y₁ =>
            cases y₂ with
            | inl q₂ => exact absurd hxy.symm (hdisj q₂ y₁)
            | inr y₂ => exact congrArg Sum.inr (hinj hxy)
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact ⟨Sum.inl (QuotientGroup.mk 1), by simp⟩
          · obtain ⟨y, hy⟩ := hmem z hz'
            exact ⟨Sum.inr y, hy⟩
        · exact isSoficAction_sum (hst x (by simp)) hY

/-- Transfer one model through an injective equivariant cover of the tested
site window.  This is the window-level core of
`isSoficAction_of_equivariant_cover`. -/
theorem exists_model_of_equivariant_cover
    (F : Finset G) (E : Finset X) (ε : ℝ) (hε : 0 < ε)
    {Y : Type u} [MulAction G Y] (f : Y → X)
    (hequiv : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hinj : Function.Injective f)
    (hmem : ∀ x ∈ E, ∃ y, f y = x)
    (hY : IsSoficAction G Y) :
    Nonempty (SoficActionModel G X F E ε) := by
  classical
  set pre : ∀ x ∈ E, Y := fun x hx => (hmem x hx).choose with hpre
  have hpre_spec : ∀ (x : X) (hx : x ∈ E), f (pre x hx) = x :=
    fun x hx => (hmem x hx).choose_spec
  set E' : Finset Y := E.attach.image (fun p => pre p.1 p.2) with hE'
  have hE'mem : ∀ (x : X) (hx : x ∈ E), pre x hx ∈ E' := by
    intro x hx
    rw [hE']
    exact Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨x, hx⟩)
  obtain ⟨M⟩ := hY F E' ε hε
  have hunique : ∀ (x : X) (hx : x ∈ E) (y : Y), f y = x → y = pre x hx := by
    intro x hx y hy
    exact hinj (by rw [hy, hpre_spec x hx])
  exact ⟨{
    Site := M.Site
    siteFintype := M.siteFintype
    siteDecEq := M.siteDecEq
    siteNonempty := M.siteNonempty
    act := M.act
    act_one := M.act_one
    act_mul := M.act_mul
    good := M.good
    good_card := M.good_card
    Chart := Option M.Chart
    chartFintype := inferInstance
    chart := fun s x => if h : ∃ y, f y = x then some (M.chart s h.choose)
      else none
    chart_inj := by
      intro s hs x hx y hy hxy
      have hex : ∃ z, f z = x := ⟨pre x hx, hpre_spec x hx⟩
      have hey : ∃ z, f z = y := ⟨pre y hy, hpre_spec y hy⟩
      rw [dif_pos hex, dif_pos hey, Option.some.injEq] at hxy
      have hxc : hex.choose = pre x hx := hunique x hx _ hex.choose_spec
      have hyc : hey.choose = pre y hy := hunique y hy _ hey.choose_spec
      rw [hxc, hyc] at hxy
      have hpreEq := M.chart_inj s hs (pre x hx) (hE'mem x hx)
        (pre y hy) (hE'mem y hy) hxy
      rw [← hpre_spec x hx, ← hpre_spec y hy, hpreEq]
    chart_equivariant := by
      intro g hg s hs hgs x hx hgx
      have hex : ∃ z, f z = x := ⟨pre x hx, hpre_spec x hx⟩
      have hegx : ∃ z, f z = g⁻¹ • x := ⟨pre _ hgx, hpre_spec _ hgx⟩
      rw [dif_pos hex, dif_pos hegx, Option.some.injEq]
      have hxc : hex.choose = pre x hx := hunique x hx _ hex.choose_spec
      have hgxc : hegx.choose = pre _ hgx := hunique _ hgx _ hegx.choose_spec
      rw [hxc, hgxc]
      have hshift : g⁻¹ • pre x hx = pre _ hgx := by
        refine hunique _ hgx _ ?_
        rw [hequiv, hpre_spec x hx]
      rw [← hshift]
      exact M.chart_equivariant g hg s hs hgs (pre x hx) (hE'mem x hx)
        (by rw [hshift]; exact hE'mem _ hgx) }⟩

/-- **Finite-window stabilizer criterion.**  A model for a given site window
only needs soficity of the transitive coset actions attached to stabilizers of
points in that window. -/
theorem exists_model_of_window_stabilizers
    (F : Finset G) (E : Finset X) (ε : ℝ) (hε : 0 < ε)
    (hst : ∀ x ∈ E, IsSoficAction G (G ⧸ MulAction.stabilizer G x)) :
    Nonempty (SoficActionModel G X F E ε) := by
  classical
  have hst' : ∀ x ∈ E.toList,
      IsSoficAction G (G ⧸ MulAction.stabilizer G x) :=
    fun x hx => hst x (Finset.mem_toList.mp hx)
  obtain ⟨Y, instY, f, hequiv, hinj, hmem, hY⟩ :=
    exists_equivariant_cover_of_list_of_mem E.toList hst'
  letI : MulAction G Y := instY
  exact exists_model_of_equivariant_cover F E ε hε f hequiv hinj
    (fun x hx => hmem x (Finset.mem_toList.mpr hx)) hY

end GroupApproximation
