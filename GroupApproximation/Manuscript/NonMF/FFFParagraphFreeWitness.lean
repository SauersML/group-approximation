import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedTheorem
import GroupApproximation.Manuscript.NonMF.TheoremCPrinted
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:torsion-free` without a simple group

`non_mf_groups_exist.tex`, `sec:torsion-free`, prints its configuration with a
subgroup `J` *isomorphic to a finitely presented infinite simple group*, and
`TorsionFreePrinted.FournierFacioParagraph` is that paragraph.  The simple
factor is the section's one genuinely new literature input: it is
`FinitelyPresentedInfiniteSimpleStatement`, which nothing inhabits, and which
Fournier-Facio's §2 cites as Burger–Mozes or Hyde–Lodha.

**The printed theorem does not need it.**  This module states the paragraph with
the simple factor replaced by a witness group carrying one distinguished element
of its commutator subgroup that survives, proves `thm:torsion-free` from that
weaker paragraph, and identifies what inhabits it.

## Where simplicity is actually used, and what replaces it

On the printed route, `TorsionFreePrinted.exists_saturatedQuotient` destructures
the paragraph as `⟨G₀, instG₀, hfp, htf, hT, hacyl, F, hΓT, -, -⟩`: it
**discards** the finite presentation and the infinitude of `J`.  What it uses of
`J` is only perfectness of `S = tJt⁻¹`, through
`PrintedFournierFacioData.commutator_simpleFactor_eq`, which is where `simple`
and `nonabelian` are consumed, and nontriviality of the normal closure of `S`.

The witness route replaces perfectness by two weaker facts: the distinguished
element lies in `⁅W, W⁆`, and its image is not `1`.  That is enough to normally
generate, and it is what `TheoremC.Configuration` already records.  A free group
of rank two with `⁅a, b⁆` satisfies it and is not perfect, so this really is a
weakening and not a restatement.

## What is here

* `FournierFacioParagraphFreeWitness` — the paragraph, with the simple factor
  replaced by the witness datum, existentially quantified exactly as
  `FournierFacioParagraph` is;
* `paragraphFreeWitness_of_configuration` and `nonempty_configuration_of_paragraph`
  — the two directions against `TheoremC.Configuration`, so nothing is lost in
  either translation;
* `printedTorsionFreeFullMFRadical_of_configuration` — the radical form of
  `thm:torsion-free` from a configuration and Hull's corrected inputs;
* `printedTorsionFreeTheorem_of_paragraphFreeWitness` — `thm:torsion-free`
  exactly as `TorsionFreePrinted.PrintedTorsionFreeTheorem` states it, from the
  weak paragraph and `HullPrintedInputs`;
* `paragraphFreeWitness_of_literatureInputs` — what inhabits the weak paragraph:
  `TheoremC.LiteratureInputs`, through `TheoremC.exists_configuration`, whose
  witness group is `FreeCommutatorWitness = F₂`.

## The two printed statements are the same statement

`TheoremC.PrintedTorsionFreeSimplified` and
`TorsionFreePrinted.PrintedTorsionFreeTheorem` are the same seven clauses in the
same order; the only difference is that the first writes the sixth as
`TheoremC.KillsAllMFTargets Q` and the second spells that definition out.
`printedTorsionFreeTheorem_of_simplified` and its converse are the two
directions, and they are what lets the assembled F₂ endpoint
`TheoremC.manuscriptTorsionFreeSimplified_openAdmissions` be read as the printed
theorem.

## Residual

Nothing here is closed on its own — every declaration carries its inputs in its
type.  What the module establishes is that the input list of `thm:torsion-free`
**loses one entry**: `FinitelyPresentedInfiniteSimpleStatement` is not needed.
What remains, after supplying `TheoremC.literatureInputs` and Hull's bundle, is
the five admissions of `Manuscript/NonMF/TheoremCAssembly.lean` — Hull's four
§5/§6 leaves and the density model — and nothing else.

## A note on `printedTorsionFreeFullMFRadical_of_configuration`

Its proof is the proof of `TheoremC.manuscriptTorsionFreeFullMFRadical` with the
single line `obtain ⟨cfg⟩ := exists_configuration I` deleted and `cfg` taken as
an argument instead; every other step is unchanged and every lemma it uses is
that module's.  The duplication is deliberate and should not outlive a decision
to give that theorem the configuration as its argument, which would make this
declaration a one-liner.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace FFFFreeWitness

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TheoremC

/-! ## The two printed statements coincide -/

/-- **`TheoremC.PrintedTorsionFreeSimplified` is `thm:torsion-free` as
`TorsionFreePrinted` states it.**

Seven clauses in the same order; the sixth is `KillsAllMFTargets Q` on one side
and its definition on the other. -/
theorem printedTorsionFreeTheorem_of_simplified
    (h : PrintedTorsionFreeSimplified) :
    TorsionFreePrinted.PrintedTorsionFreeTheorem := by
  obtain ⟨Q, instQ, h2, hfp, htf, hah, hT, hkills, hquot⟩ := h
  exact ⟨Q, instQ, h2, hfp, htf, hah, hT, hkills, hquot⟩

/-- The converse, so that the identification is an equivalence and neither
statement is the weaker one. -/
theorem printedTorsionFreeSimplified_of_theorem
    (h : TorsionFreePrinted.PrintedTorsionFreeTheorem) :
    PrintedTorsionFreeSimplified := by
  obtain ⟨Q, instQ, h2, hfp, htf, hah, hT, hkills, hquot⟩ := h
  exact ⟨Q, instQ, h2, hfp, htf, hah, hT, hkills, hquot⟩

/-! ## The paragraph, with the simple factor replaced -/

/-- **The Fournier-Facio paragraph with a witness factor in place of the simple
factor.**

Compare `TorsionFreePrinted.FournierFacioParagraph`.  The four adjectives on
`G₀` are the same.  In place of *"a subgroup `J ≤ G₀` isomorphic to a finitely
presented infinite simple group"* this asks only for a group `W`, a homomorphism
`W → G₀`, and one distinguished `d ∈ ⁅W, W⁆` with `witness d ≠ 1`; the three
printed relations become `witness x ∈ range core`, `t · core p · t⁻¹ ∈ range
core`, and commutation of the witness image with `t · core · t⁻¹`.

This is `TheoremC.Configuration` written as a proposition, and it is strictly
weaker than the printed paragraph in the only clause that differs: a finitely
presented infinite simple group is perfect, so any nonidentity element of it
lies in its commutator subgroup, while `W` here need not be perfect. -/
def FournierFacioParagraphFreeWitness : Prop :=
  ∃ (G₀ : Type) (_ : Group G₀), Group.IsFinitelyPresented G₀ ∧
    IsPowerTorsionFree G₀ ∧ HasKazhdanPropertyT.{0, 0} G₀ ∧
      IsAcylindricallyHyperbolic G₀ ∧
        ∃ (Core W : Type) (_ : Group Core) (_ : Group W)
          (core : Core →* G₀) (witness : W →* G₀) (t : G₀) (d : W),
          HasKazhdanPropertyT.{0, 0} Core ∧
            d ∈ _root_.commutator W ∧
              witness d ≠ 1 ∧
                (∀ x : W, ∃ p : Core, witness x = core p) ∧
                  (∀ p : Core, ∃ q : Core, t * core p * t⁻¹ = core q) ∧
                    (∀ (x : W) (p : Core),
                      Commute (witness x) (t * core p * t⁻¹))

/-- Every `TheoremC.Configuration` gives the paragraph. -/
theorem paragraphFreeWitness_of_configuration (C : Configuration) :
    FournierFacioParagraphFreeWitness :=
  ⟨C.Ambient, C.groupAmbient, C.fpAmbient, C.torsionFreeAmbient, C.kazhdanAmbient,
    C.acylAmbient, C.Core, C.Witness, C.groupCore, C.groupWitness, C.core,
    C.witness, C.t, C.distinguished, C.kazhdanCore, C.distinguished_mem_commutator,
    C.distinguished_image_ne_one, C.core_mem_of_witness, C.t_compresses,
    C.witness_commute_conj⟩

/-- And conversely, so the translation loses nothing. -/
theorem nonempty_configuration_of_paragraph
    (h : FournierFacioParagraphFreeWitness) : Nonempty Configuration := by
  obtain ⟨G₀, instG₀, hfp, htf, hT, hacyl, Core, W, instCore, instW, core,
    witness, t, d, hCoreT, hd, hdne, hmem, hcompress, hcomm⟩ := h
  exact ⟨{ Ambient := G₀
           groupAmbient := instG₀
           fpAmbient := hfp
           torsionFreeAmbient := htf
           kazhdanAmbient := hT
           acylAmbient := hacyl
           Witness := W
           groupWitness := instW
           Core := Core
           groupCore := instCore
           kazhdanCore := hCoreT
           core := core
           witness := witness
           distinguished := d
           distinguished_mem_commutator := hd
           distinguished_image_ne_one := hdne
           core_mem_of_witness := hmem
           t := t
           t_compresses := hcompress
           witness_commute_conj := hcomm }⟩

/-! ## `thm:torsion-free` from a configuration -/

/-- **The radical form of `thm:torsion-free`, from a configuration and Hull's
corrected inputs.**

The proof of `TheoremC.manuscriptTorsionFreeFullMFRadical` with
`obtain ⟨cfg⟩ := exists_configuration I` replaced by the argument `cfg`. -/
theorem printedTorsionFreeFullMFRadical_of_configuration (cfg : Configuration)
    (hHull : HullCorrectedInputs.HullInputsCorrected.{0}) :
    PrintedTorsionFreeFullMFRadical := by
  haveI : Countable cfg.Ambient := cfg.countableAmbient
  let W : Subgroup cfg.Ambient := (_root_.commutator cfg.Witness).map cfg.witness
  have hNne := witnessCommutatorNormalClosure_ne_bot cfg
  have hFin : ({1, cfg.witness cfg.distinguished} : Set cfg.Ambient).Finite :=
    (Set.finite_singleton (cfg.witness cfg.distinguished)).insert 1
  obtain ⟨SQ⟩ := TorsionFree.saturation hHull cfg.torsionFreeAmbient
    (Subgroup.normalClosure (↑W : Set cfg.Ambient)) hNne hFin
  haveI : Countable SQ.Q := SQ.surjective.countable
  have hQT : HasKazhdanPropertyT.{0, 0} SQ.Q :=
    HasKazhdanPropertyT.of_surjective SQ.q SQ.surjective cfg.kazhdanAmbient
  have hmem1 : (1 : cfg.Ambient) ∈
      ({1, cfg.witness cfg.distinguished} : Set cfg.Ambient) :=
    Set.mem_insert _ _
  have hmems : cfg.witness cfg.distinguished ∈
      ({1, cfg.witness cfg.distinguished} : Set cfg.Ambient) :=
    Set.mem_insert_of_mem _ rfl
  have hqs : SQ.q (cfg.witness cfg.distinguished) ≠ 1 := by
    intro hz
    apply cfg.distinguished_image_ne_one
    have h1 : SQ.q (cfg.witness cfg.distinguished) = SQ.q 1 := by
      rw [hz, map_one]
    exact SQ.injOn hmems hmem1 h1
  haveI : Nontrivial SQ.Q :=
    ⟨⟨SQ.q (cfg.witness cfg.distinguished), 1, hqs⟩⟩
  have hmain : ∀ (L : Type) (_ : Group L) (r : SQ.Q →* L),
      Function.Surjective r → Nontrivial L →
        manuscriptCoronaMFResidual L = ⊤ := by
    intro L instL r hr hLne
    letI := instL
    haveI := hLne
    haveI : Countable L := hr.countable
    refine coronaMFResidual_eq_top_of_normallyGenerating cfg (r.comp SQ.q)
      (hr.comp SQ.surjective) ?_
    rw [← Subgroup.map_map, SQ.map_eq_top]
    exact Subgroup.map_top_of_surjective r hr
  refine ⟨SQ.Q, inferInstance,
    ⟨SQ.generatorOne, SQ.generatorTwo, SQ.twoGenerated⟩, inferInstance,
    SQ.torsionFree, inferInstance, hQT, ?_, hmain, ?_⟩
  · exact hmain SQ.Q inferInstance (MonoidHom.id SQ.Q) Function.surjective_id
      inferInstance
  · intro L instL r hr hLne hMF
    letI := instL
    haveI := hLne
    haveI : Countable L := hr.countable
    have htop := hmain L instL r hr hLne
    have hbot : manuscriptCoronaMFResidual L = ⊥ :=
      isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp
        ((isCDEOperatorMF_iff_isOperatorMF L).mpr hMF)
    obtain ⟨x, hx⟩ := exists_ne (1 : L)
    apply hx
    have hmem : x ∈ manuscriptCoronaMFResidual L := by
      rw [htop]
      exact Subgroup.mem_top x
    rw [hbot] at hmem
    simpa using hmem

/-! ## The printed theorem, without a simple group -/

/-- **`thm:torsion-free`, exactly as `TorsionFreePrinted` states it, from the
paragraph with a witness factor and Hull's printed inputs.**

> There is a two-generated, finitely presented, torsion-free, acylindrically
> hyperbolic group `Q` with property (T) such that every homomorphism from `Q`
> to an MF group is trivial.  In particular, no nontrivial quotient of `Q` is
> MF.

The two hypotheses are the section's Hull citation and a paragraph that asks for
**no simple group**.  Compare
`TorsionFreePrinted.manuscriptTorsionFreeTheorem`, which takes
`FournierFacioParagraph` in place of the first, and whose only route to an
inhabitant runs through `FinitelyPresentedInfiniteSimpleStatement`. -/
theorem printedTorsionFreeTheorem_of_paragraphFreeWitness
    (h : FournierFacioParagraphFreeWitness)
    (hHull : TorsionFreePrinted.HullPrintedInputs.{0}) :
    TorsionFreePrinted.PrintedTorsionFreeTheorem := by
  obtain ⟨cfg⟩ := nonempty_configuration_of_paragraph h
  obtain ⟨Q, instQ, h2, hfp, htf, hah, hT, hrad, -, -⟩ :=
    printedTorsionFreeFullMFRadical_of_configuration cfg hHull.toCorrected
  letI := instQ
  haveI : Group.IsFinitelyPresented Q := hfp
  haveI : Countable Q := ChiodoBelegradek.countable_of_isFinitelyPresented Q
  have hkills : KillsAllMFTargets Q := by
    intro M instM hM f x
    letI := instM
    exact OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets Q M hrad hM f x
  refine ⟨Q, instQ, h2, hfp, htf, hah, hT, hkills, ?_⟩
  intro L instL r hr hL
  letI := instL
  haveI := hL
  exact quotient_not_isOperatorMF_of_killsMFTargets hkills r hr

/-! ## What inhabits the weak paragraph -/

/-- **`TheoremC.LiteratureInputs` inhabits the paragraph.**

`TheoremC.exists_configuration` builds a configuration whose witness group is
`FreeCommutatorWitness`, the free group of rank two, with `⁅a, b⁆` as the
distinguished element.  So the weak paragraph costs exactly the five citations
of the earlier printed construction and nothing more; in particular it does not
cost `FinitelyPresentedInfiniteSimpleStatement`. -/
theorem paragraphFreeWitness_of_literatureInputs (I : LiteratureInputs) :
    FournierFacioParagraphFreeWitness := by
  obtain ⟨cfg⟩ := exists_configuration I
  exact paragraphFreeWitness_of_configuration cfg

/-- **`thm:torsion-free` from the earlier construction's citations alone.**

Neither hypothesis mentions a simple group.  Supplying
`TheoremC.literatureInputs` for `I` reduces this to the five admissions of
`Manuscript/NonMF/TheoremCAssembly.lean`; `hHull` is Hull's Theorem 7.1 with
Osin's Lemma 7.1, which those admissions also carry in corrected form. -/
theorem printedTorsionFreeTheorem_of_literatureInputs (I : LiteratureInputs)
    (hHull : TorsionFreePrinted.HullPrintedInputs.{0}) :
    TorsionFreePrinted.PrintedTorsionFreeTheorem :=
  printedTorsionFreeTheorem_of_paragraphFreeWitness
    (paragraphFreeWitness_of_literatureInputs I) hHull

end FFFFreeWitness
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFFreeWitness.printedTorsionFreeTheorem_of_simplified

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFFreeWitness.printedTorsionFreeSimplified_of_theorem

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFFreeWitness.printedTorsionFreeFullMFRadical_of_configuration

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFFreeWitness.printedTorsionFreeTheorem_of_paragraphFreeWitness

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFFreeWitness.printedTorsionFreeTheorem_of_literatureInputs
