import GroupApproximation.Computability.ModularMachineConfigHalting
import GroupApproximation.Computability.WordProblemRE
import GroupApproximation.Computability.TorsionFreeMFMarkov

/-!
# `NONMF ∉ RE`: MF recognition is algorithmically impossible

Write `MF` for the set of finite presentations whose group is operator-MF and
`NONMF` for its complement, both taken in the recursive coding
`PresentationCodes.PresentationCode` of finite presentations --- a generator
count together with a finite list of relator words.  `PresentationCodes.Carrier`
reads the presented group off a code syntactically, and every coded group is
finitely presented, so "decide MF from a finite presentation" is a statement
about a `Primcodable` type and a predicate on it rather than about an
arbitrary indexing.

This file states the two headline consequences in closed form, with no
hypothesis and no construction datum accepted from a caller:

* `mf_recognition_not_computable` --- `MF` is not a computable predicate;
* `no_mf_decider` --- equivalently, no computable `Bool`-valued program agrees
  with MF-ness on every finite presentation;
* `nonMF_presentations_not_re` --- **`NONMF ∉ RE`**: the non-MF finite
  presentations are not a recursively enumerable set;
* `no_nonMF_enumerator` --- equivalently, no program prints non-MF
  presentations only and is guaranteed to eventually print every one of them.
* `no_nonMF_certificate_system` --- equivalently again, no type of finite
  certificates with a computable checker is both sound and complete for
  non-MF-ness.

`mf_recognition_impossible` packages all of it as a single proposition.

## Where each half comes from

Both halves travel through one computable transformation
`AdianRabinVariantTransform.reduction`, whose correctness clause is the
equivalence

    the group of `Δ (P, w)` is MF   ↔   `w = 1` in the group of `P`

for the uniform word problem `W` on presentation codes.  So `Δ` is a
many-one reduction `W ≤₀ MF` and simultaneously `Wᶜ ≤₀ NONMF`;
`exists_manyOne_reduction_wordProblem_to_operatorMF` records both orientations
at once, which is the precise sense in which `NONMF` is coRE-hard.

The source facts pulled back through `Δ` are:

* `Computability.not_computablePred_wordProblemPred` --- `W` is undecidable,
  by way of the repository's own Boone group and modular machine;
* `WordProblemRE.not_rePred_compl_wordProblemPred` --- `Wᶜ ∉ RE`, which is
  Post's theorem applied to `WordProblemRE.rePred_wordProblemPred` (`W ∈ RE`)
  against the previous item.

The r.e. set in this argument is the **word problem**, at the source of the
reduction.  Nothing here asserts that `MF` itself is recursively enumerable;
that is a separate question this file does not touch, and the second headline
does not need it.

The Markov data the reduction is built from is likewise internal: MF-ness is
inherited by subgroups (`IsOperatorMF.comap`), free groups are MF, the trivial
group is MF (`PresentationCodes.isOperatorMF_positiveCode`), and there is a
finitely presented group that is not
(`PresentationCodes.not_isOperatorMF_negativeCode`, backed by
`ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF`).

## Scope of the enumeration statement

`no_nonMF_enumerator` is about **presentations**, matching the set `NONMF`: an
enumerator is refuted when it prints only non-MF codes and every non-MF code
eventually appears.  A list carrying one presentation per isomorphism class of
non-MF finitely presented groups is a different object, since isomorphism of
coded groups is itself not decidable; no claim is made about it here.

The enumerator is allowed to output `Option PresentationCode`, so a program
that runs forever while printing only finitely often is covered too, and
`no_total_nonMF_enumerator` specializes to a program that prints at every step.

## Manuscript status

Closed forms of the manuscript's `cor:undecidable`.  Both sentences of that
corollary are endpoints here, together with the two "no program" restatements
and the many-one reduction that names the hardness.
-/

namespace GroupApproximation
namespace MFRecognitionImpossible

open PresentationCodes MarkovMFConsequences

/-! ## The domain: codes really are finite presentations -/

/-- Every presentation code names a finitely presented group, so the two
theorems below are statements about finite presentations. -/
theorem isFinitelyPresented_carrier (c : PresentationCode) :
    Group.IsFinitelyPresented (Carrier c) :=
  inferInstance

/-- A code whose group is operator-MF: the trivial group. -/
theorem exists_mf_presentation :
    ∃ c : PresentationCode, IsOperatorMF (Carrier c) :=
  ⟨positiveCode, isOperatorMF_positiveCode⟩

/-- A code whose group is not operator-MF: the repository's finitely presented
non-MF group, transported to the coding. -/
theorem exists_nonMF_presentation :
    ∃ c : PresentationCode, ¬ IsOperatorMF (Carrier c) :=
  ⟨negativeCode, not_isOperatorMF_negativeCode⟩

/-! ## The reduction, and the hardness it names -/

/-- **One computable transformation reduces the uniform word problem to MF
recognition, in both orientations.**

The first clause is `W ≤₀ MF`; the second is `Wᶜ ≤₀ NONMF`, which is the
statement that `NONMF` is coRE-hard under many-one reductions. -/
theorem exists_manyOne_reduction_wordProblem_to_operatorMF :
    ∃ Δ : PresentationCode × List (ℕ × Bool) → PresentationCode,
      Computable Δ ∧
      (∀ x, AdianRabinWordProblem.wordProblemPred x ↔
        IsOperatorMF (Carrier (Δ x))) ∧
      (∀ x, ¬ AdianRabinWordProblem.wordProblemPred x ↔
        ¬ IsOperatorMF (Carrier (Δ x))) := by
  refine ⟨AdianRabinVariantTransform.reduction.transform,
    AdianRabinVariantTransform.reduction.transform_computable, ?_, ?_⟩
  · intro x
    exact (AdianRabinVariantTransform.reduction.correct x).symm.trans
      (operatorMFProperty_semantics _)
  · intro x
    exact not_congr ((AdianRabinVariantTransform.reduction.correct x).symm.trans
      (operatorMFProperty_semantics _))

/-- **The halting problem of a fixed machine many-one reduces to MF
recognition.**  A computable compiler turns each configuration of one fixed
modular machine --- whose configuration-halting problem is undecidable, by
Mathlib's halting problem through this repository's machine chain --- into a
finite presentation whose group is MF exactly when that configuration halts.

This is the reduction carried the whole way, from a machine to a presentation:
the third clause is `Halt ≤₀ MF` and the fourth is `Haltᶜ ≤₀ NONMF`.  It says
nothing about which level of the arithmetical hierarchy `MF` sits at, only that
it is at least as hard as this halting set. -/
theorem exists_halting_reduction_to_operatorMF :
    ∃ (mm : BooneGroup.ModularMachine) (Ψ : ℕ × ℕ → PresentationCode),
      (¬ ComputablePred fun p : ℕ × ℕ => mm.Halts p) ∧
      Computable Ψ ∧
      (∀ p, IsOperatorMF (Carrier (Ψ p)) ↔ mm.Halts p) ∧
      (∀ p, ¬ IsOperatorMF (Carrier (Ψ p)) ↔ ¬ mm.Halts p) := by
  obtain ⟨mm, hmm⟩ :=
    Computability.exists_modularMachine_config_halting_not_computablePred
  have hM : (mm.size : ℤ) ≠ 0 := by exact_mod_cast mm.size_pos.ne'
  obtain ⟨w, hw, hspec⟩ := Computability.exists_boone_words mm hM
  have hiff : ∀ p : ℕ × ℕ,
      IsOperatorMF (Carrier (AdianRabinVariantTransform.reduction.transform
        (Computability.finalGroupCode mm hM, w p))) ↔ mm.Halts p := fun p =>
    (operatorMFProperty_semantics _).symm.trans
      ((AdianRabinVariantTransform.reduction.correct _).trans (hspec p))
  exact ⟨mm, fun p => AdianRabinVariantTransform.reduction.transform
      (Computability.finalGroupCode mm hM, w p), hmm,
    AdianRabinVariantTransform.reduction.transform_computable.comp
      (Computable.pair (Computable.const _) hw),
    hiff, fun p => not_congr (hiff p)⟩

/-! ## MF recognition is undecidable -/

/-- **MF-ness of a finite presentation is not a computable predicate.** -/
theorem mf_recognition_not_computable :
    ¬ ComputablePred fun c : PresentationCode => IsOperatorMF (Carrier c) := by
  intro h
  exact Computability.operatorMF_recognition_not_computable
    (h.of_eq fun c => (operatorMFProperty_semantics c).symm)

/-- **There is no algorithm which takes a finite group presentation and decides
whether it is MF.**  This is `mf_recognition_not_computable` spelled out as the
nonexistence of a correct `Bool`-valued program. -/
theorem no_mf_decider :
    ¬ ∃ f : PresentationCode → Bool,
        Computable f ∧ ∀ c, f c = true ↔ IsOperatorMF (Carrier c) := by
  rintro ⟨f, hf, hcorrect⟩
  exact mf_recognition_not_computable
    (ComputablePred.computable_iff.mpr
      ⟨f, hf, funext fun c => propext (hcorrect c).symm⟩)

/-! ## `NONMF ∉ RE` -/

/-- **The non-MF finite presentations are not recursively enumerable.**

`NONMF ∉ RE`, at the recursive coding of finite presentations. -/
theorem nonMF_presentations_not_re :
    ¬ REPred fun c : PresentationCode => ¬ IsOperatorMF (Carrier c) := by
  intro h
  exact WordProblemRE.operatorMF_negative_side_not_re
    (h.of_eq fun c => (not_congr (operatorMFProperty_semantics c)).symm)

/-- **No program prints exactly the non-MF finite presentations.**

The program is modelled as a computable `f : ℕ → Option PresentationCode`:
step `n` either prints a presentation or prints nothing, so a program that
prints only finitely often is covered.  Soundness is "everything printed is a
non-MF presentation" and completeness is "every non-MF presentation is
eventually printed"; no computable `f` has both. -/
theorem no_nonMF_enumerator :
    ¬ ∃ f : ℕ → Option PresentationCode,
        Computable f ∧
        (∀ n c, f n = some c → ¬ IsOperatorMF (Carrier c)) ∧
        (∀ c, ¬ IsOperatorMF (Carrier c) → ∃ n, f n = some c) := by
  rintro ⟨f, hf, hsound, hcomplete⟩
  have hbase : Computable
      fun p : Option PresentationCode × Option PresentationCode =>
        decide (p.1 = p.2) :=
    (PrimrecRel.comp Primrec.eq Primrec.fst Primrec.snd).decide.to_comp
  have hg : Computable₂ fun (c : PresentationCode) (n : ℕ) =>
      decide (f n = some c) :=
    hbase.comp (Computable.pair (hf.comp Computable.snd)
      (Computable.option_some.comp Computable.fst))
  refine nonMF_presentations_not_re
    ((WordProblemRE.rePred_exists_eq_true hg).of_eq fun c => ?_)
  constructor
  · rintro ⟨n, hn⟩
    exact hsound n c (of_decide_eq_true hn)
  · intro hc
    obtain ⟨n, hn⟩ := hcomplete c hc
    exact ⟨n, decide_eq_true hn⟩

/-- **There is no sound and complete recursively checkable certificate system
for non-MF-ness.**

A certificate system is a type of proofs together with a computable checker
`V`.  Soundness and completeness together say that a presentation is non-MF
exactly when some certificate passes the check.  No such system exists, for any
type of certificates whatsoever: this is `nonMF_presentations_not_re` read as a
statement about proof systems rather than about enumerations, and it is what
rules out ever exhibiting non-MF-ness by a finite checkable witness. -/
theorem no_nonMF_certificate_system :
    ¬ ∃ (Cert : Type) (_ : Primcodable Cert) (V : PresentationCode → Cert → Bool),
        Computable₂ V ∧
        ∀ c, (∃ π, V c π = true) ↔ ¬ IsOperatorMF (Carrier c) := by
  rintro ⟨Cert, hCert, V, hV, hspec⟩
  exact nonMF_presentations_not_re
    ((WordProblemRE.rePred_exists_eq_true hV).of_eq hspec)

/-- **No program keeps printing non-MF presentations and eventually prints
every one of them.**  The `Option`-free specialization of
`no_nonMF_enumerator`, for a program that prints at every step. -/
theorem no_total_nonMF_enumerator :
    ¬ ∃ f : ℕ → PresentationCode,
        Computable f ∧
        (∀ n, ¬ IsOperatorMF (Carrier (f n))) ∧
        (∀ c, ¬ IsOperatorMF (Carrier c) → ∃ n, f n = c) := by
  rintro ⟨f, hf, hsound, hcomplete⟩
  refine no_nonMF_enumerator
    ⟨fun n => some (f n), Computable.option_some.comp hf, ?_, ?_⟩
  · intro n c hn
    have hn' : f n = c := Option.some_inj.mp hn
    subst hn'
    exact hsound n
  · intro c hc
    obtain ⟨n, hn⟩ := hcomplete c hc
    exact ⟨n, congrArg Option.some hn⟩

/-! ## The package -/

/-- **MF recognition is algorithmically impossible, as one closed
proposition.**

The clauses are, in order: MF is not decidable from a finite presentation; no
`Bool`-valued program decides it; `NONMF ∉ RE`; no program enumerates the
non-MF presentations; every code names a finitely presented group; no
certificate system is sound and complete for non-MF-ness; and both sides are
inhabited, so neither statement is about an empty set. -/
theorem mf_recognition_impossible :
    (¬ ComputablePred fun c : PresentationCode => IsOperatorMF (Carrier c)) ∧
      (¬ ∃ f : PresentationCode → Bool,
          Computable f ∧ ∀ c, f c = true ↔ IsOperatorMF (Carrier c)) ∧
      (¬ REPred fun c : PresentationCode => ¬ IsOperatorMF (Carrier c)) ∧
      (¬ ∃ f : ℕ → Option PresentationCode,
          Computable f ∧
          (∀ n c, f n = some c → ¬ IsOperatorMF (Carrier c)) ∧
          (∀ c, ¬ IsOperatorMF (Carrier c) → ∃ n, f n = some c)) ∧
      (∀ c : PresentationCode, Group.IsFinitelyPresented (Carrier c)) ∧
      (¬ ∃ (Cert : Type) (_ : Primcodable Cert)
          (V : PresentationCode → Cert → Bool),
          Computable₂ V ∧
          ∀ c, (∃ π, V c π = true) ↔ ¬ IsOperatorMF (Carrier c)) ∧
      (∃ c : PresentationCode, IsOperatorMF (Carrier c)) ∧
      (∃ c : PresentationCode, ¬ IsOperatorMF (Carrier c)) :=
  ⟨mf_recognition_not_computable, no_mf_decider, nonMF_presentations_not_re,
    no_nonMF_enumerator, isFinitelyPresented_carrier, no_nonMF_certificate_system,
    exists_mf_presentation, exists_nonMF_presentation⟩

/-! ## The torsion-free refinement

The same two sentences hold for the conjunction "torsion-free and MF", whose
Markov data is `TorsionFreeMFMarkov.torsionFreeMFMarkovData`.  Both were stated
there with the two computability facts as premises; both premises are theorems
of this repository, so both statements close. -/

/-- Recognising "torsion-free and operator-MF" from a finite presentation is
undecidable. -/
theorem torsionFreeMF_recognition_not_computable :
    ¬ ComputablePred (AdianRabinGeneral.codeProperty
      (fun (H : Type) (_ : Group H) => IsPowerTorsionFree H ∧ IsOperatorMF H)) :=
  TorsionFreeMFMarkov.torsionFreeMF_recognition_undecidable
    Computability.not_computablePred_wordProblemPred

/-- The presentations failing "torsion-free and operator-MF" are not
recursively enumerable. -/
theorem torsionFreeMF_negative_side_not_re :
    ¬ REPred fun c : PresentationCode =>
      ¬ (IsPowerTorsionFree (Carrier c) ∧ IsOperatorMF (Carrier c)) :=
  TorsionFreeMFMarkov.torsionFreeMF_negative_side_not_re
    WordProblemRE.not_rePred_compl_wordProblemPred

end MFRecognitionImpossible
end GroupApproximation
