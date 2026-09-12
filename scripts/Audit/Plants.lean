import Lean

/-!
# Planted defects, for calibrating the scans

gnomon runs a calibration before every detector whose verdict it reads, and
states the reason in each CI step: a detector that reports nothing is
indistinguishable from a clean corpus, so its silence is not evidence until
both directions are asserted.  Its laundering, identity-gate, round-trip,
metamorphic and correspondence guards each have one of these.

This is that corpus for `Audit.Scan`.  Every declaration below is either a
defect that a named scan must report, or a clean declaration that no scan may
report -- and the second half is not decoration.  It is what fails when a scan
stops distinguishing and starts alarming at everything, which is the failure
mode a zero-tolerance gate quietly rewards.

`scripts/Calibrate.lean` asserts both directions, and CI runs it BEFORE the
real audit.  This module is deliberately Mathlib-free, so the calibration
holds even when the corpus does not build.
-/

namespace AuditPlant

/-! ## Defects.  Each must be reported, under the tag named in its comment. -/

/-- AXIOM: a hand-declared axiom in the corpus. -/
axiom plantedAxiom : True

/-- TAUTOLOGY: the conclusion is the premise, under a name claiming the
conclusion.  Note that its `#print axioms` is perfectly clean, which is why the
dependency scan cannot see it. -/
theorem plantedTautology (h : 0 = 0) : 0 = 0 := h

/-- UNCONDITIONAL: the name promises existence; the type still takes a
premise. -/
theorem plantedExistsUnderPremise (h : (0 : Nat) = 0) : ∃ n : Nat, n = 0 :=
  ⟨0, h⟩

/-- INSTANCE_PREMISE: a Prop premise in implicit syntax, invisible to a reader
skimming the signature. -/
theorem plantedHiddenPremise {h : (0 : Nat) = 0} : (0 : Nat) = 0 ∧ True :=
  ⟨h, trivial⟩

/-- EMPTY_PREMISE: vacuously true, and provable for the same reason whatever
the conclusion says. -/
theorem plantedVacuous (h : False) : (0 : Nat) = 1 := h.elim

set_option linter.unusedVariables false in
/-- TRIVIAL + UNUSED: concludes `True`, and its premise occurs in neither the
rest of the type nor the proof term.

The linter is disabled for this declaration alone, and `h` deliberately keeps
its leading-underscore-free name: the underscore is exactly the admission the
UNUSED scan accepts (`Audit.Scan.deliberate`), so a plant that spelled it `_h`
would no longer be the defect it exists to plant.  Renaming the binder or
widening this `set_option` past the one declaration silently decalibrates the
UNUSED scan. -/
theorem plantedUnusedHypothesis (h : (0 : Nat) = 0) : True := trivial

/-- STALE_DISCLAIMER: a conditional result, or so this sentence claims --
the statement below has no premise to be conditional on. -/
theorem plantedStaleDisclaimer : ∃ n : Nat, n = 1 := ⟨1, rfl⟩

/-- DUPLICATE + RFL. -/
theorem plantedDuplicateA : (1 : Nat) + 1 = 2 := rfl

/-- DUPLICATE + RFL: the same proposition under a second name. -/
theorem plantedDuplicateB : (1 : Nat) + 1 = 2 := rfl

/-- The axiom traversal must descend through PROOF TERMS, not merely notice
declarations that are themselves axioms.  This theorem's type mentions no
axiom; only its proof reaches `Classical.choice`.  Asserted directly in
`scripts/Calibrate.lean`, because the plain axiom plant above passes even when
the descent is completely broken. -/
theorem plantedReachesClassical (p : Prop) (h : ¬¬p) : p :=
  Classical.byContradiction h

/-- Must be UNCONDITIONAL: a headline claim word, at the root of the corpus
namespace, on a type that still takes a premise. -/
theorem plantedNonsoficUnconditional (h : (0 : Nat) = 0) : ∃ n : Nat, n = 0 :=
  ⟨0, h⟩

/-- Must be ASSUMPTION_INSTANCE: an assumption written in instance syntax. -/
theorem plantedNonemptyAssumption [Nonempty Nat] : True := trivial

/-- Must NOT be RFL: a `@[simp]` lemma proved by `rfl` is a deliberate API
lemma, which is what 96 of the corpus's 96 hits were. -/
@[simp] theorem plantedSimpRfl : (2 : Nat) + 0 = 2 := rfl

/-! ## Clean declarations.  No scan may report any of these. -/

/-- Not UNUSED: Lean's own convention for a deliberately unused binder is the
leading underscore, which its `unusedVariables` linter respects.  Honouring it
keeps the scan silent without an allow-list, and makes the underscore
an admission a reader can grep for rather than a way around the check. -/
theorem cleanDeliberateUnused (_h : (0 : Nat) = 0) : (1 : Nat) ≤ 1 :=
  Nat.le_refl 1

/-- Not TAUTOLOGY: the conclusion genuinely uses the premise without being
it. -/
theorem cleanUsesPremise (h : (0 : Nat) = 0) : (0 : Nat) = 0 ∧ (1 : Nat) = 1 :=
  ⟨h, rfl⟩

/-- Not STALE_DISCLAIMER: this result really is conditional, and the premise it
is conditional on is right there in the type.  This is the shape the source-text
version of the scan could not distinguish, and the reason it moved into the
environment -- four sentences of this shape in the real corpus were its only
findings, every one of them true. -/
theorem cleanConditionalOnItsPremise (h : (0 : Nat) = 0) : ∃ n : Nat, n = 0 :=
  ⟨0, h⟩

/-- The conditional expectation is scalar.  This uses the technical noun
"conditional expectation" and makes no claim about proof status. -/
theorem cleanConditionalExpectation : ∃ n : Nat, n = 2 := ⟨2, rfl⟩

/-! ## Literature-input plants

The real roster of tagged transcriptions is driver config; the calibration
tags `PlantedLiteratureInput` below, so it needs no corpus.  The witness
matters because the literature scan must distinguish proving a tagged input
from assuming it downstream. -/

/-- The planted stand-in for a literature transcription. -/
def PlantedLiteratureInput : Prop := ∀ n : Nat, n = n

/-- Its satisfiability witness; a non-`rfl` proof, so the RFL scan stays
calibrated.  Must NOT be LITERATURE_INPUT: a conclusion whose head is the
tagged proposition is a proof of it, not an assumption of it. -/
theorem plantedLiteratureWitness : PlantedLiteratureInput :=
  fun _ => Eq.trans rfl rfl

/-- LITERATURE_INPUT: takes the transcription as a premise. -/
theorem plantedLiteratureConditional (h : PlantedLiteratureInput) : 0 = 0 :=
  h 0

/-- One definitional layer of laundering. -/
def PlantedLiteratureAlias : Prop := PlantedLiteratureInput

/-- Must NOT be LITERATURE_INPUT: proving the alias is proving the
transcription. -/
theorem plantedLiteratureAliasWitness : PlantedLiteratureAlias :=
  plantedLiteratureWitness

/-- LITERATURE_INPUT: the premise mentions the transcription only through the
alias, which the closure must not be fooled by. -/
theorem plantedLiteratureLaundered (h : PlantedLiteratureAlias) : 1 = 1 :=
  h 1

/-- LITERATURE_INPUT: the conclusion embeds the transcription under a
connective instead of proving it outright, which is how a conditional claim
hides without taking a premise. -/
theorem plantedLiteratureEmbedded : PlantedLiteratureInput ∨ 0 = 1 :=
  Or.inl plantedLiteratureWitness

/-- A wrapper structure carrying the transcription as a field: the second
laundering channel, through a constructor type rather than a definition
body. -/
structure PlantedLiteraturePacket : Prop where
  input : PlantedLiteratureInput

/-- Must NOT be LITERATURE_INPUT: a conclusion whose head reaches the tagged
input is a proof of the packet, not a use of it as an assumption. -/
theorem plantedLiteraturePacketWitness : PlantedLiteraturePacket :=
  ⟨plantedLiteratureWitness⟩

/-- LITERATURE_INPUT: the premise mentions the transcription only through the
packet's constructor field. -/
theorem plantedLiteraturePacketed (h : PlantedLiteraturePacket) : 0 = 0 :=
  h.input 0

end AuditPlant
