import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.PrintedHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.TuringDegree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LEFCorollaries.RecursiveHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ToeplitzAnswer
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Pestov91.LEFHyperlinear
import GroupApproximation.Meta.AxiomGuard

/-!
# The abstract of `simple_kazhdan_sofic_group.tex`, claim by claim (A1)

`simple_kazhdan_sofic_group.tex`, abstract (tex l.32–47):

> Infinite simple groups with property (T) can be limits of finite simple groups. For every infinite
> minimal subshift `X`, the group `G_X = EL_3(LC(X, F₂) ⋊ ℤ)` is an infinite, finitely generated,
> simple group with property (T) and a limit of finite simple groups `SL_{3N}(F₂)` whose Cayley graphs
> form expanders, so it is locally embeddable into finite groups (LEF), sofic and hyperlinear. This
> answers the question of Brown and Ozawa whether an infinite simple Kazhdan group can be hyperlinear,
> and Pestov's sofic version of it. A finitely generated group is LEF if and only if it is a subgroup
> of an infinite, finitely generated, simple Kazhdan group that is a limit of finite simple groups
> whose Cayley graphs form expanders, and the host can be chosen with a word problem of the same Turing
> degree as that of the group. One such host contains every recursively presented finitely generated
> LEF group.

## Spelling

* "A limit of finite simple groups whose Cayley graphs form expanders" is ThmMainA's printed notion
  `ThmMainA.IsExpanderLimitOfClass` (tex l.86–100) for the class `IsFiniteSimpleClass` of finite simple
  groups.
* "Such a host" is `IsAbstractHost`: infinite, finitely generated, simple, Kazhdan, and such a limit.
  Lane 12's `SK12.IsPrintedHost` (the class `SL_N(F₂)`, `cor:lef`) is stronger
  (`isAbstractHost_of_isPrintedHost`).
* LEF is the printed `IsTextbookLEF` (tex l.102–104). Sofic and hyperlinear are the corpus `IsSofic`
  and `IsHyperlinear`.

## Closed statements

1. `AbstractSimpleKazhdanLimits` (l.33–34), witnessed by `G_X` for the Toeplitz subshift.
2. `AbstractGX` (l.34–38): Theorem `thm:main` in both printed spellings, and `AbstractSoConsequence`
   (l.38: "so it is LEF, sofic and hyperlinear").
3. `AbstractBrownOzawaPestov` (l.39–40).
4. `AbstractLEFIffSubgroup` (l.41–43).
5. `AbstractSameTuringDegreeHost` (l.43–45).
6. `AbstractRecursivelyPresentedHost` (l.45–46).

`PrintedAbstract` bundles them and `printedAbstract` proves it. Every proof reuses closed theorems.
None of them takes a hypothesis standing in for a literature result.
-/

namespace GroupApproximation.Full.SK05

open GroupApproximation.SimpleKazhdanSofic
open SymbolicDynamics.FullShift

/-! ## The class of finite simple groups and the host -/

/-- The class of **finite simple groups** (abstract, tex l.33–34 and l.42–43). -/
def IsFiniteSimpleClass (Q : Type) [Group Q] : Prop :=
  Finite Q ∧ IsSimpleGroup Q

/-- **Such a host** (abstract, tex l.41–43): an infinite, finitely generated, simple Kazhdan group that
is a limit of finite simple groups whose Cayley graphs form expanders. -/
def IsAbstractHost (E : Type) [Group E] : Prop :=
  Infinite E ∧ Group.FG E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
    ThmMainA.IsExpanderLimitOfClass IsFiniteSimpleClass E

/-- An expander limit of groups from a class `C` is an expander limit of groups from any larger
class `D`. -/
theorem isExpanderLimitOfClass_mono {C D : ∀ (Q : Type) [Group Q], Prop}
    (hCD : ∀ (Q : Type) [Group Q], C Q → D Q) {E : Type*} [Group E]
    (h : ThmMainA.IsExpanderLimitOfClass C E) : ThmMainA.IsExpanderLimitOfClass D E := by
  obtain ⟨m, g, Q, _, q, hC, hlim⟩ := h
  exact ⟨m, g, Q, inferInstance, q, fun k => hCD (Q k) (hC k), hlim⟩

/-- The finite simple groups `SL_{nN}(F₂)` are finite simple groups. -/
theorem isFiniteSimpleClass_of_multiple (n : ℕ) (Q : Type) [Group Q]
    (h : IsFiniteSimpleSLMultiple n Q) : IsFiniteSimpleClass Q :=
  ⟨h.1, h.2.1⟩

/-- The finite simple groups `SL_N(F₂)` of `cor:lef` are finite simple groups. -/
theorem isFiniteSimpleClass_of_sl (Q : Type) [Group Q] (h : SK12.IsFiniteSimpleSL Q) :
    IsFiniteSimpleClass Q :=
  ⟨h.1, h.2.1⟩

/-- A printed host of `cor:lef` (limit of `SL_N(F₂)`) is a host in the sense of the abstract. -/
theorem isAbstractHost_of_isPrintedHost {E : Type} [Group E] (h : SK12.IsPrintedHost E) :
    IsAbstractHost E := by
  obtain ⟨hinf, hfg, hsimple, hT, hlim⟩ := h
  exact ⟨hinf, hfg, hsimple, hT, isExpanderLimitOfClass_mono isFiniteSimpleClass_of_sl hlim⟩

/-- **tex l.38** (*so it is LEF, sofic and hyperlinear*): a limit of finite groups whose Cayley graphs
form expanders is LEF, sofic and hyperlinear. -/
theorem lef_sofic_hyperlinear_of_expanderLimit {C : ∀ (Q : Type) [Group Q], Prop} {E : Type}
    [Group E] (h : ThmMainA.IsExpanderLimitOfClass C E) :
    IsTextbookLEF E ∧ IsLEF E ∧ IsSofic E ∧ IsHyperlinear E := by
  obtain ⟨_, g, _, _, q, -, hlim⟩ := h
  have hT : IsTextbookLEF E :=
    ThmMainA.manuscriptSentence_limitsOfFiniteGroupsAreLEF q g hlim.2.1 hlim.1
  have hL : IsLEF E := (isLEF_iff_textbook E).2 hT
  exact ⟨hT, hL, isSofic_of_isLEF hL, Pestov91.isHyperlinear_of_isLEF hL⟩

/-! ## Claim 1 (tex l.33–34) -/

/-- **Abstract, tex l.33–34.** *Infinite simple groups with property (T) can be limits of finite
simple groups.* -/
def AbstractSimpleKazhdanLimits : Prop :=
  ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
    ThmMainA.IsExpanderLimitOfClass IsFiniteSimpleClass E

/-- **Abstract, tex l.33–34**, closed: `G_X` for the Toeplitz subshift is such a group. -/
theorem abstractSimpleKazhdanLimits : AbstractSimpleKazhdanLimits := by
  obtain ⟨hinf, -, hsimple, hT, hlim, -, -, -⟩ :=
    main_el Bool toeplitzSubshift toeplitzSubshift_infinite toeplitzSubshift_isMinimal 3 le_rfl
  exact ⟨EL 3 toeplitzSubshift, inferInstance, hinf, hsimple, hT,
    isExpanderLimitOfClass_mono (isFiniteSimpleClass_of_multiple 3) hlim⟩

/-! ## Claim 2 (tex l.34–38) -/

/-- **Abstract, tex l.38**, closed: *so it is LEF, sofic and hyperlinear.* Every limit of finite
simple groups whose Cayley graphs form expanders is LEF, sofic and hyperlinear. -/
def AbstractSoConsequence : Prop :=
  ∀ (E : Type) [Group E], ThmMainA.IsExpanderLimitOfClass IsFiniteSimpleClass E →
    IsTextbookLEF E ∧ IsLEF E ∧ IsSofic E ∧ IsHyperlinear E

/-- **Abstract, tex l.38**, closed. -/
theorem abstractSoConsequence : AbstractSoConsequence := by
  intro E _ h
  exact lef_sofic_hyperlinear_of_expanderLimit h

/-- **Abstract, tex l.34–38.** *For every infinite minimal subshift `X`, `G_X` is an infinite, finitely
generated, simple group with property (T) and a limit of finite simple groups `SL_{3N}(F₂)` whose
Cayley graphs form expanders, so it is LEF, sofic and hyperlinear*: Theorem `thm:main` in the spelling
of `Endpoints.lean` and in Lane 1's printed spelling, together with the general implication. -/
def AbstractGX : Prop :=
  PrintedMainTheorem ∧ PrintedMainTheoremSK01 ∧ AbstractSoConsequence

/-- **Abstract, tex l.34–38**, closed. -/
theorem abstractGX : AbstractGX :=
  ⟨printedMainTheorem, printedMainTheoremSK01, abstractSoConsequence⟩

/-! ## Claim 3 (tex l.39–40) -/

/-- **Abstract, tex l.39–40.** *This answers the question of Brown and Ozawa whether an infinite simple
Kazhdan group can be hyperlinear, and Pestov's sofic version of it*: there are infinite simple Kazhdan
groups that are hyperlinear, there are ones that are sofic, and `G_X` for a (Toeplitz) infinite minimal
subshift is both. -/
def AbstractBrownOzawaPestov : Prop :=
  (∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
      IsHyperlinear E) ∧
    (∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
      IsSofic E) ∧
    PrintedGXAnswersBrownOzawaPestov

/-- **Abstract, tex l.39–40**, closed. -/
theorem abstractBrownOzawaPestov : AbstractBrownOzawaPestov := by
  have hGX : PrintedGXAnswersBrownOzawaPestov := printedGXAnswersBrownOzawaPestov_of_main
    SimpleKazhdanSofic.printedSimpleKazhdanSoficMain
  obtain ⟨S, -, -, hinf, hsimple, hT, hsofic, hhyp⟩ := hGX
  exact ⟨⟨SimpleKazhdanSofic.G S, inferInstance, hinf, hsimple, hT, hhyp⟩,
    ⟨SimpleKazhdanSofic.G S, inferInstance, hinf, hsimple, hT, hsofic⟩,
    printedGXAnswersBrownOzawaPestov_of_main
    SimpleKazhdanSofic.printedSimpleKazhdanSoficMain⟩

/-! ## Claim 4 (tex l.41–43) -/

/-- **Abstract, tex l.41–43.** *A finitely generated group is LEF if and only if it is a subgroup of an
infinite, finitely generated, simple Kazhdan group that is a limit of finite simple groups whose Cayley
graphs form expanders.* -/
def AbstractLEFIffSubgroup : Prop :=
  ∀ (Γ : Type) [Group Γ], Group.FG Γ →
    (IsTextbookLEF Γ ↔
      ∃ (E : Type) (_ : Group E), IsAbstractHost E ∧ ∃ f : Γ →* E, Function.Injective f)

/-- **Abstract, tex l.41–43**, closed. The forward direction gives the stronger host of `cor:lef`
(`SK12.corLef_lefIffSubgroupOfHost`). -/
theorem abstractLEFIffSubgroup : AbstractLEFIffSubgroup := by
  intro Γ _ hfg
  constructor
  · intro hΓ
    obtain ⟨E, _, hE, f, hf⟩ := (SK12.corLef_lefIffSubgroupOfHost Γ hfg).1 hΓ
    exact ⟨E, inferInstance, isAbstractHost_of_isPrintedHost hE, f, hf⟩
  · rintro ⟨E, _, hE, f, hf⟩
    exact SK12.isTextbookLEF_of_injective f hf
      (lef_sofic_hyperlinear_of_expanderLimit hE.2.2.2.2).1

/-! ## Claim 5 (tex l.43–45) -/

/-- **Abstract, tex l.43–45.** *The host can be chosen with a word problem of the same Turing degree as
that of the group*: for every finite generating family `t` of `Γ` and `s` of the host, the word problem
oracles are Turing equivalent. -/
def AbstractSameTuringDegreeHost : Prop :=
  ∀ (Γ : Type) [Group Γ], Group.FG Γ → IsTextbookLEF Γ →
    ∃ (E : Type) (_ : Group E), IsAbstractHost E ∧ ∃ f : Γ →* E, Function.Injective f ∧
      ∀ (κ ι : Type) [Primcodable κ] [Primcodable ι] [Finite κ] [Finite ι] (t : κ → Γ)
        (s : ι → E), Subgroup.closure (Set.range t) = ⊤ → Subgroup.closure (Set.range s) = ⊤ →
          TuringEquivalent (wordProblemOracle t) (wordProblemOracle s)

/-- **Abstract, tex l.43–45**, closed, from `SK12.corLef_lefIffSubgroupOfSameTuringDegreeHost`. -/
theorem abstractSameTuringDegreeHost : AbstractSameTuringDegreeHost := by
  intro Γ _ hfg hΓ
  obtain ⟨E, _, hE, f, hf, hdeg⟩ :=
    (SK12.corLef_lefIffSubgroupOfSameTuringDegreeHost Γ hfg).1 hΓ
  exact ⟨E, inferInstance, isAbstractHost_of_isPrintedHost hE, f, hf, hdeg⟩

/-! ## Claim 6 (tex l.45–46) -/

/-- **Abstract, tex l.45–46.** *One such host contains every recursively presented finitely generated
LEF group.* -/
def AbstractRecursivelyPresentedHost : Prop :=
  ∃ (E : Type) (_ : Group E), IsAbstractHost E ∧
    ∀ (Γ : Type) [Group Γ], Group.FG Γ → Nonempty (Higman.RecursivePresentation Γ) →
      IsTextbookLEF Γ → ∃ f : Γ →* E, Function.Injective f

/-- **Abstract, tex l.45–46**, closed, from `SK12.corHost_recursivelyPresentedInstances`. -/
theorem abstractRecursivelyPresentedHost : AbstractRecursivelyPresentedHost := by
  obtain ⟨E, _, hE, hrec, -, -⟩ := SK12.corHost_recursivelyPresentedInstances
  exact ⟨E, inferInstance, isAbstractHost_of_isPrintedHost hE, hrec⟩

/-! ## The whole abstract -/

/-- **The abstract** (tex l.32–47), all six claims. -/
def PrintedAbstract : Prop :=
  AbstractSimpleKazhdanLimits ∧ AbstractGX ∧ AbstractBrownOzawaPestov ∧ AbstractLEFIffSubgroup ∧
    AbstractSameTuringDegreeHost ∧ AbstractRecursivelyPresentedHost

/-- **The abstract** (tex l.32–47), closed. -/
theorem printedAbstract : PrintedAbstract :=
  ⟨abstractSimpleKazhdanLimits, abstractGX, abstractBrownOzawaPestov, abstractLEFIffSubgroup,
    abstractSameTuringDegreeHost, abstractRecursivelyPresentedHost⟩

end GroupApproximation.Full.SK05

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.Full.SK05.isExpanderLimitOfClass_mono
#audit_axioms GroupApproximation.Full.SK05.isAbstractHost_of_isPrintedHost
#audit_axioms GroupApproximation.Full.SK05.lef_sofic_hyperlinear_of_expanderLimit
#audit_closed_axioms GroupApproximation.Full.SK05.abstractSimpleKazhdanLimits
#audit_closed_axioms GroupApproximation.Full.SK05.abstractSoConsequence
#audit_closed_axioms GroupApproximation.Full.SK05.abstractGX
#audit_closed_axioms GroupApproximation.Full.SK05.abstractBrownOzawaPestov
#audit_closed_axioms GroupApproximation.Full.SK05.abstractLEFIffSubgroup
#audit_closed_axioms GroupApproximation.Full.SK05.abstractSameTuringDegreeHost
#audit_closed_axioms GroupApproximation.Full.SK05.abstractRecursivelyPresentedHost
#audit_closed_axioms GroupApproximation.Full.SK05.printedAbstract
