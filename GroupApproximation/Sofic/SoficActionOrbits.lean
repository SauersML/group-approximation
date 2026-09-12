import GroupApproximation.Sofic.SoficActionSum
import GroupApproximation.Sofic.SoficActionChabauty
import GroupApproximation.Sofic.CoAmenableActionSofic
import GroupApproximation.Sofic.AscendingHNNCosetActionSofic
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Lemma 30.4 in full: gluing arbitrary orbits

A finite window meets only finitely many orbits, so an action all of whose
transitive pieces are sofic is sofic.  The bookkeeping is done with injective
equivariant maps rather than with subsets: for a finite window one builds a
finite iterated sum of coset spaces together with an injective equivariant map
onto the orbits met by the window, and a model for the sum is a model for the
window.

This closes the step Section 30.5 needs -- from sofic coset actions to *all*
actions -- for LERF groups, and the same statement powers Theorem 30.7 for LERA
groups.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G]

/-! ## The empty action -/

theorem isSoficAction_of_isEmpty {Y : Type v} [MulAction G Y] [IsEmpty Y] :
    IsSoficAction G Y := by
  classical
  intro F E ε hε
  exact ⟨{
    Site := PUnit.{v + 1}
    siteFintype := inferInstance
    siteDecEq := inferInstance
    siteNonempty := by simp
    act := fun _ => 1
    act_one := rfl
    act_mul := by
      intro g _ h _
      simpa using hε.le
    good := Finset.univ
    good_card := by
      simp only [Finset.card_univ]
      have hcard : (Fintype.card PUnit.{v + 1} : ℝ) = 1 := by simp
      rw [hcard]
      linarith
    Chart := PUnit.{v + 1}
    chartFintype := inferInstance
    chart := fun _ _ => PUnit.unit
    chart_inj := by
      intro _ _ x _ _ _ _
      exact (IsEmpty.false x).elim
    chart_equivariant := by
      intro _ _ _ _ _ x _ _
      exact (IsEmpty.false x).elim }⟩

/-! ## Transfer along an injective equivariant map -/

/-- If every finite window is covered by an injective equivariant image of a
sofic action, the action is sofic.  The model for the source serves the target:
the charts are read through the (unique) preimages. -/
theorem isSoficAction_of_equivariant_cover {X : Type u} [MulAction G X]
    (hcov : ∀ E : Finset X, ∃ (Y : Type u) (_ : MulAction G Y) (f : Y → X),
      (∀ (g : G) (y : Y), f (g • y) = g • f y) ∧ Function.Injective f ∧
      (∀ x ∈ E, ∃ y, f y = x) ∧ IsSoficAction G Y) :
    IsSoficAction G X := by
  classical
  intro F E ε hε
  obtain ⟨Y, instY, f, hequiv, hinj, hmem, hY⟩ := hcov E
  letI : MulAction G Y := instY
  -- the window pulled back through the cover
  set pre : ∀ x ∈ E, Y := fun x hx => (hmem x hx).choose with hpre
  have hpre_spec : ∀ (x : X) (hx : x ∈ E), f (pre x hx) = x :=
    fun x hx => (hmem x hx).choose_spec
  set E' : Finset Y := E.attach.image (fun p => pre p.1 p.2) with hE'
  have hE'mem : ∀ (x : X) (hx : x ∈ E), pre x hx ∈ E' := by
    intro x hx
    rw [hE']
    exact Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨x, hx⟩)
  obtain ⟨M⟩ := hY F E' ε hε
  -- the unique preimage of a covered point
  have hunique : ∀ (x : X) (hx : x ∈ E) (y : Y), f y = x → y = pre x hx := by
    intro x hx y hy
    exact hinj (by rw [hy, hpre_spec x hx])
  refine ⟨{
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
    chart_inj := ?_
    chart_equivariant := ?_ }⟩
  · intro s hs x hx y hy hxy
    have hex : ∃ z, f z = x := ⟨pre x hx, hpre_spec x hx⟩
    have hey : ∃ z, f z = y := ⟨pre y hy, hpre_spec y hy⟩
    rw [dif_pos hex, dif_pos hey, Option.some.injEq] at hxy
    have hxc : hex.choose = pre x hx := hunique x hx _ hex.choose_spec
    have hyc : hey.choose = pre y hy := hunique y hy _ hey.choose_spec
    rw [hxc, hyc] at hxy
    have := M.chart_inj s hs (pre x hx) (hE'mem x hx) (pre y hy) (hE'mem y hy) hxy
    rw [← hpre_spec x hx, ← hpre_spec y hy, this]
  · intro g hg s hs hgs x hx hgx
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
      (by rw [hshift]; exact hE'mem _ hgx)

/-! ## Orbits as coset spaces -/

variable {X : Type u} [MulAction G X]

/-- The orbit map of a point, as a map from the coset space of its
stabilizer. -/
def orbitMap (x : X) : G ⧸ MulAction.stabilizer G x → X := fun q =>
  Quotient.liftOn' q (fun g : G => g • x) (by
    intro a b hab
    have h : a⁻¹ * b ∈ MulAction.stabilizer G x :=
      QuotientGroup.leftRel_apply.mp hab
    have hx : (a⁻¹ * b) • x = x := h
    calc a • x = a • ((a⁻¹ * b) • x) := by rw [hx]
      _ = b • x := by rw [smul_smul, mul_inv_cancel_left])

@[simp] theorem orbitMap_mk (x : X) (g : G) :
    orbitMap x (QuotientGroup.mk g) = g • x := rfl

theorem orbitMap_equivariant (x : X) (g : G)
    (q : G ⧸ MulAction.stabilizer G x) :
    orbitMap x (g • q) = g • orbitMap x q := by
  induction q using QuotientGroup.induction_on with
  | _ a =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, orbitMap_mk, orbitMap_mk,
      mul_smul]

theorem orbitMap_injective (x : X) :
    Function.Injective (orbitMap (G := G) x) := by
  intro q₁ q₂ h
  induction q₁ using QuotientGroup.induction_on with
  | _ a =>
    induction q₂ using QuotientGroup.induction_on with
    | _ b =>
      rw [orbitMap_mk, orbitMap_mk] at h
      refine QuotientGroup.eq.mpr ?_
      show (a⁻¹ * b) • x = x
      rw [mul_smul, ← h, inv_smul_smul]

/-! ## Gluing the orbits met by a finite window -/

theorem exists_equivariant_cover_of_list
    (hst : ∀ x : X, IsSoficAction G (G ⧸ MulAction.stabilizer G x)) :
    ∀ l : List X, ∃ (Y : Type u) (_ : MulAction G Y) (f : Y → X),
      (∀ (g : G) (y : Y), f (g • y) = g • f y) ∧ Function.Injective f ∧
      (∀ x ∈ l, ∃ y, f y = x) ∧ IsSoficAction G Y := by
  classical
  intro l
  induction l with
  | nil =>
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
      obtain ⟨Y, instY, f, hequiv, hinj, hmem, hY⟩ := ih
      letI : MulAction G Y := instY
      by_cases hx : ∃ y, f y = x
      · refine ⟨Y, instY, f, hequiv, hinj, ?_, hY⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hx
        · exact hmem z hz'
      · -- a new orbit: it is disjoint from what is already covered
        letI : DecidableEq X := Classical.decEq _
        letI : DecidableEq Y := Classical.decEq _
        letI : DecidableEq (G ⧸ MulAction.stabilizer G x) := Classical.decEq _
        refine ⟨(G ⧸ MulAction.stabilizer G x) ⊕ Y, inferInstance,
          Sum.elim (orbitMap x) f, ?_, ?_, ?_, ?_⟩
        · intro g y
          cases y with
          | inl q => exact orbitMap_equivariant x g q
          | inr y => exact hequiv g y
        · intro y₁ y₂ h
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
              exact congrArg Sum.inl (orbitMap_injective x h)
            | inr y₂ => exact absurd h (hdisj q₁ y₂)
          | inr y₁ =>
            cases y₂ with
            | inl q₂ => exact absurd h.symm (hdisj q₂ y₁)
            | inr y₂ => exact congrArg Sum.inr (hinj h)
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact ⟨Sum.inl (QuotientGroup.mk 1), by simp⟩
          · obtain ⟨y, hy⟩ := hmem z hz'
            exact ⟨Sum.inr y, hy⟩
        · exact isSoficAction_sum (hst x) hY

/-- **Lemma 30.4, general form.**  An action all of whose point stabilizers
have sofic coset actions is sofic. -/
theorem isSoficAction_of_stabilizers
    (hst : ∀ x : X, IsSoficAction G (G ⧸ MulAction.stabilizer G x)) :
    IsSoficAction G X := by
  classical
  refine isSoficAction_of_equivariant_cover fun E => ?_
  obtain ⟨Y, instY, f, hequiv, hinj, hmem, hY⟩ :=
    exists_equivariant_cover_of_list hst E.toList
  exact ⟨Y, instY, f, hequiv, hinj,
    fun x hx => hmem x (Finset.mem_toList.mpr hx), hY⟩

/-! ## Universally action-sofic groups -/

/-- **Theorem 30.5.**  If every subgroup of `G` is separable, every action of
`G` on any set is sofic. -/
theorem universallyActionSofic_of_separable
    (hsep : ∀ (H : Subgroup G) (g : G), g ∉ H →
      ∃ K : Subgroup G, H ≤ K ∧ K.FiniteIndex ∧ g ∉ K) :
    MarkedCompression.UniversallyActionSofic G := by
  intro Y _
  exact isSoficAction_of_stabilizers fun y =>
    isSoficAction_quotient_of_separable _ (hsep _)

/-- **Theorem 30.7.**  Every action of a LERA group on any set is sofic. -/
theorem universallyActionSofic_of_isLERA (h : IsLERA G) :
    MarkedCompression.UniversallyActionSofic G := by
  intro Y _
  exact isSoficAction_of_stabilizers fun y =>
    isSoficAction_quotient_of_isLERA h _

/-- Amenable groups are universally action-sofic, by Lemma 30.6 -- recovered
here through the LERA route. -/
theorem universallyActionSofic_of_isAmenable
    (hG : Amenability.IsAmenable G) :
    MarkedCompression.UniversallyActionSofic G :=
  universallyActionSofic_of_isLERA (isLERA_of_isAmenable hG)

end GroupApproximation
