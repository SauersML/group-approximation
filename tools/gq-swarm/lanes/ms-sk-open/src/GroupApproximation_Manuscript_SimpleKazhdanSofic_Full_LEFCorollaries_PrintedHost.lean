import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThmMainA.MarkedGroups
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFCharacterizationClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:lef` (first statement) and `cor:host` (first two statements), in the printed words

`simple_kazhdan_sofic_group.tex`, Section `sec:lef`:

> **Corollary (`cor:lef`)** (l.453–461). A finitely generated group is LEF if and only if it is a
> subgroup of an infinite, finitely generated, simple Kazhdan group that is an expander limit of
> finite simple groups `SL_N(F₂)`. [...]
>
> **Corollary (`cor:host`)** (l.463–470). Every countable LEF group is a subgroup of such a group.
> The members of a set of finitely generated groups embed in a single such group if and only if
> they are LEF and represent countably many isomorphism classes. [...]
>
> **Proof** (l.589–601). Limits of finite groups in the space of marked groups are LEF, and so are
> their subgroups. [...]

## Spelling

* LEF is the printed definition `IsTextbookLEF` (tex l.102–104).
* "Expander limit of groups from a class" is ThmMainA's printed notion
  `ThmMainA.IsExpanderLimitOfClass` (tex l.92–100): convergence in the space of marked groups, finite
  groups of unbounded order, and a uniform vertex-expansion constant.
* "Finite simple groups `SL_N(F₂)`" is the class `IsFiniteSimpleSL`: finite simple groups isomorphic to
  the special linear group over `F₂` on a finite index type of size `N`.
* `IsPrintedHost E` is "such a group".
* "Subgroup of" means an injective homomorphism into the host.
* "Represent countably many isomorphism classes" means some countable family of groups contains an
  isomorphic copy of every member.

## Proof route

The closed corpus theorems `printedLEFSubgroupCharacterization`, `printedCountableLEFHost` and
`printedLEFFamilyHost` are stated for the corpus host `IsLEFHost` (a marked limit of `SL_{κ ℓ}(F₂)` with
edge-expanding Cayley graphs). `isPrintedHost_of_isLEFHost` converts it into the printed host through
`ThmMainA.isExpanderLimit_of_isMarkedLimit`. The converse directions use only the printed notions:
`isTextbookLEF_of_isPrintedHost` is tex l.591 ("limits of finite groups ... are LEF") through
`ThmMainA.manuscriptSentence_limitsOfFiniteGroupsAreLEF`, and `isTextbookLEF_of_injective` is "and so
are their subgroups".
-/

namespace GroupApproximation.Full.SK12

open GroupApproximation.SimpleKazhdanSofic

universe u

/-! ## The printed host -/

/-- The class of **finite simple groups `SL_N(F₂)`** (tex l.456): finite simple groups isomorphic to
the special linear group over `F₂` on a finite index type of size `N`. -/
def IsFiniteSimpleSL (Q : Type) [Group Q] : Prop :=
  Finite Q ∧ IsSimpleGroup Q ∧
    ∃ (N : ℕ) (n : Type) (_ : Fintype n) (_ : DecidableEq n), Fintype.card n = N ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup n (ZMod 2))

/-- **Such a group** (tex l.454–456): an infinite, finitely generated, simple Kazhdan group that is
an expander limit (tex l.92–100) of finite simple groups `SL_N(F₂)`. -/
def IsPrintedHost (E : Type) [Group E] : Prop :=
  Infinite E ∧ Group.FG E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
    ThmMainA.IsExpanderLimitOfClass IsFiniteSimpleSL E

/-- **Subgroups of LEF groups are LEF**, for the printed definition. -/
theorem isTextbookLEF_of_injective {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) (hK : IsTextbookLEF K) : IsTextbookLEF H :=
  (isLEF_iff_textbook H).mp (isLEF_of_injective f hf ((isLEF_iff_textbook K).mpr hK))

#audit_axioms GroupApproximation.Full.SK12.isTextbookLEF_of_injective

/-- The corpus host `IsLEFHost` is a printed host: its marked limit with an edge-expanding family of
Cayley graphs is an expander limit in the printed sense, and the `SL_{κ ℓ}(F₂)` lie in the class of
finite simple groups `SL_N(F₂)` with `N = |κ ℓ|`. -/
theorem isPrintedHost_of_isLEFHost {E : Type} [Group E] (h : IsLEFHost E) : IsPrintedHost E := by
  obtain ⟨hinf, hfg, hsimple, hT, _, _, κ, _, _, _, hSL, hlim, hexp⟩ := h
  obtain ⟨m, g, q, hq⟩ := ThmMainA.isExpanderLimit_of_isMarkedLimit hlim hexp
  refine ⟨hinf, hfg, hsimple, hT, m, g, fun ℓ => Matrix.SpecialLinearGroup (κ ℓ) (ZMod 2),
    fun _ => inferInstance, q, fun ℓ => ?_, hq⟩
  exact ⟨hq.2.1 ℓ, hSL ℓ, Fintype.card (κ ℓ), κ ℓ, inferInstance, inferInstance, rfl,
    ⟨MulEquiv.refl _⟩⟩

#audit_axioms GroupApproximation.Full.SK12.isPrintedHost_of_isLEFHost

/-- **tex l.591.** *Limits of finite groups in the space of marked groups are LEF*: a printed host is
LEF. -/
theorem isTextbookLEF_of_isPrintedHost {E : Type} [Group E] (h : IsPrintedHost E) :
    IsTextbookLEF E := by
  obtain ⟨-, -, -, -, _, g, _, _, q, -, hq⟩ := h
  exact ThmMainA.manuscriptSentence_limitsOfFiniteGroupsAreLEF q g hq.2.1 hq.1

#audit_axioms GroupApproximation.Full.SK12.isTextbookLEF_of_isPrintedHost

/-- **tex l.591–592.** *Limits of finite groups in the space of marked groups are LEF, and so are
their subgroups*, in the printed notions: if `(G, g)` is the limit of marked finite groups
`(Q k, q k)`, then every subgroup of `G` is LEF. -/
theorem manuscriptSentence_limitsAndSubgroupsLEF {m : ℕ} {Q : ℕ → Type} [∀ k, Group (Q k)]
    (q : ∀ k, Fin m → Q k) {G : Type} [Group G] (g : Fin m → G) (hfin : ∀ k, Finite (Q k))
    (hconv : ThmMainA.MarkedConverges q g) :
    IsTextbookLEF G ∧ ∀ K : Subgroup G, IsTextbookLEF ↥K := by
  have hG : IsTextbookLEF G := ThmMainA.manuscriptSentence_limitsOfFiniteGroupsAreLEF q g hfin hconv
  exact ⟨hG, fun K => isTextbookLEF_of_injective K.subtype K.subtype_injective hG⟩

#audit_axioms GroupApproximation.Full.SK12.manuscriptSentence_limitsAndSubgroupsLEF

/-! ## `cor:lef`, first statement -/

/-- **`cor:lef`, first statement** (tex l.454–456): a finitely generated group is LEF if and only if
it is a subgroup of an infinite, finitely generated, simple Kazhdan group that is an expander limit of
finite simple groups `SL_N(F₂)`. -/
theorem corLef_lefIffSubgroupOfHost (Γ : Type) [Group Γ] (hfg : Group.FG Γ) :
    IsTextbookLEF Γ ↔
      ∃ (E : Type) (_ : Group E), IsPrintedHost E ∧ ∃ f : Γ →* E, Function.Injective f := by
  constructor
  · intro hΓ
    obtain ⟨E, _, hE, f, hf⟩ :=
      (printedLEFSubgroupCharacterization Γ hfg).1 ((isLEF_iff_textbook Γ).2 hΓ)
    exact ⟨E, inferInstance, isPrintedHost_of_isLEFHost hE, f, hf⟩
  · rintro ⟨E, _, hE, f, hf⟩
    exact isTextbookLEF_of_injective f hf (isTextbookLEF_of_isPrintedHost hE)

#audit_axioms GroupApproximation.Full.SK12.corLef_lefIffSubgroupOfHost

/-! ## `cor:host`, first and second statements -/

/-- **`cor:host`, first statement** (tex l.464): every countable LEF group is a subgroup of such a
group. -/
theorem corHost_countableLEFSubgroupOfHost (Γ : Type) [Group Γ] (hc : Countable Γ)
    (hΓ : IsTextbookLEF Γ) :
    ∃ (E : Type) (_ : Group E), IsPrintedHost E ∧ ∃ f : Γ →* E, Function.Injective f := by
  obtain ⟨E, _, hE, f, hf⟩ := printedCountableLEFHost Γ hc ((isLEF_iff_textbook Γ).2 hΓ)
  exact ⟨E, inferInstance, isPrintedHost_of_isLEFHost hE, f, hf⟩

#audit_axioms GroupApproximation.Full.SK12.corHost_countableLEFSubgroupOfHost

/-- **`cor:host`, second statement** (tex l.464–466): the members of a set of finitely generated
groups embed in a single such group if and only if they are LEF and represent countably many
isomorphism classes.

Forward (tex l.591–592 and l.597–598): the members are subgroups of a LEF group, and a finitely
generated host is countable, so it has countably many finitely generated subgroups, and each member is
isomorphic to its image. Backward: the closed corpus theorem `printedLEFFamilyHost`. -/
theorem corHost_familyEmbedsIffLEFCountableClasses {ι : Type u} (Γ : ι → Type)
    [∀ i, Group (Γ i)] (hfg : ∀ i, Group.FG (Γ i)) :
    (∃ (E : Type) (_ : Group E), IsPrintedHost E ∧ ∀ i, ∃ f : Γ i →* E, Function.Injective f) ↔
      (∀ i, IsTextbookLEF (Γ i)) ∧
        ∃ (J : Type) (_ : Countable J) (H : J → Type) (_ : ∀ j, Group (H j)),
          ∀ i, ∃ j, Nonempty (Γ i ≃* H j) := by
  constructor
  · rintro ⟨E, _, hE, hemb⟩
    refine ⟨fun i => ?_, ?_⟩
    · obtain ⟨f, hf⟩ := hemb i
      exact isTextbookLEF_of_injective f hf (isTextbookLEF_of_isPrintedHost hE)
    · haveI : Group.FG E := hE.2.1
      haveI : Countable E := ContinuumMultiplicity.countable_of_fg E
      refine ⟨↥{K : Subgroup E | K.FG}, (ContinuumMultiplicity.countable_fg_subgroups E).to_subtype,
        fun j => ↥(j : Subgroup E), fun _ => inferInstance, fun i => ?_⟩
      obtain ⟨f, hf⟩ := hemb i
      haveI : Group.FG (Γ i) := hfg i
      have hrange : f.range.FG := (Group.fg_iff_subgroup_fg f.range).mp (Group.fg_range f)
      exact ⟨⟨f.range, hrange⟩, ⟨MonoidHom.ofInjective hf⟩⟩
  · rintro ⟨hlef, hcls⟩
    obtain ⟨E, _, hE, hemb⟩ :=
      (printedLEFFamilyHost.{u} ι Γ hfg).2 ⟨fun i => (isLEF_iff_textbook (Γ i)).2 (hlef i), hcls⟩
    exact ⟨E, inferInstance, isPrintedHost_of_isLEFHost hE, hemb⟩

#audit_axioms GroupApproximation.Full.SK12.corHost_familyEmbedsIffLEFCountableClasses

end GroupApproximation.Full.SK12
