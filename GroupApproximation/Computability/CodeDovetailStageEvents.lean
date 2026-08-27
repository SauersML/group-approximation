import GroupApproximation.Computability.ExactLiteralEFinInfSwitch
import GroupApproximation.Computability.SecondLevelIndexSets
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Interval.Finset.Defs

/-!
# A computable dovetail stream for partial-recursive domains

Each input in the domain of a partial-recursive code emits exactly one event:
at the least evaluator stage at which that input halts.  The event address is
the pairing of the input with that least stage.  Consequently the event stream
is unbounded exactly when the program domain is infinite, and it has a final
cut exactly when the program domain is finite.

The Boolean stream itself is primitive recursive uniformly in the program
code.  No enumeration or embedding theorem is used here.
-/

namespace GroupApproximation
namespace CodeDovetailStageEvents

open Nat.Partrec
open SecondLevelIndexSets
open ExactLiteralEFinInfSwitch

/-- `firstHaltsAt c n stage` detects the unique first evaluator stage at which
input `n` of code `c` has acquired a value. -/
def firstHaltsAt (c : Code) (n stage : ℕ) : Bool :=
  (Code.evaln stage c n).isSome && !(Code.evaln (stage - 1) c n).isSome

/-- Pair the input and evaluator stage into one literal event address. -/
def dovetailEvent (c : Code) (address : ℕ) : Bool :=
  firstHaltsAt c (Nat.unpair address).1 (Nat.unpair address).2

/-- The stage-event stream uniformly associated to a partial-recursive code. -/
def codeStageEvents (c : Code) : StageEvents where
  event := dovetailEvent c

/-- The dovetail event matrix is primitive recursive, uniformly in both the
program code and event address. -/
theorem primrec_dovetailEvent : Primrec₂ dovetailEvent := by
  have hcode : Primrec fun z : Code × ℕ => z.1 := Primrec.fst
  have haddress : Primrec fun z : Code × ℕ => z.2 := Primrec.snd
  have hunpair : Primrec fun z : Code × ℕ => Nat.unpair z.2 :=
    Primrec.unpair.comp haddress
  have hinput : Primrec fun z : Code × ℕ => (Nat.unpair z.2).1 :=
    Primrec.fst.comp hunpair
  have hstage : Primrec fun z : Code × ℕ => (Nat.unpair z.2).2 :=
    Primrec.snd.comp hunpair
  have hprevious : Primrec fun z : Code × ℕ => (Nat.unpair z.2).2 - 1 :=
    Primrec.nat_sub.comp hstage (Primrec.const 1)
  have hnow : Primrec fun z : Code × ℕ =>
      Code.evaln (Nat.unpair z.2).2 z.1 (Nat.unpair z.2).1 :=
    Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair hstage hcode) hinput)
  have hbefore : Primrec fun z : Code × ℕ =>
      Code.evaln ((Nat.unpair z.2).2 - 1) z.1 (Nat.unpair z.2).1 :=
    Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair hprevious hcode) hinput)
  exact (Primrec.and.comp
    (Primrec.option_isSome.comp hnow)
    (Primrec.not.comp (Primrec.option_isSome.comp hbefore))).of_eq fun _ => rfl

theorem computable_dovetailEvent : Computable₂ dovetailEvent :=
  primrec_dovetailEvent.to_comp

theorem firstHaltsAt_eq_true_iff (c : Code) (n stage : ℕ) :
    firstHaltsAt c n stage = true ↔
      (Code.evaln stage c n).isSome = true ∧
        (Code.evaln (stage - 1) c n).isSome = false := by
  simp [firstHaltsAt]

/-- Two first-halting witnesses for one input necessarily name the same
evaluator stage. -/
theorem firstHaltsAt_stage_unique (c : Code) (n s t : ℕ)
    (hs : firstHaltsAt c n s = true) (ht : firstHaltsAt c n t = true) :
    s = t := by
  rw [firstHaltsAt_eq_true_iff] at hs ht
  have not_lt : ¬ s < t := by
    intro hst
    have hle : s ≤ t - 1 := by omega
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (by simpa using hs.1)
    have hx' := Code.evaln_mono hle hx
    have hsome : (Code.evaln (t - 1) c n).isSome = true := by
      simpa using Option.isSome_iff_exists.mpr ⟨x, hx'⟩
    exact Bool.noConfusion (hsome.symm.trans ht.2)
  have not_gt : ¬ t < s := by
    intro hts
    have hle : t ≤ s - 1 := by omega
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (by simpa using ht.1)
    have hx' := Code.evaln_mono hle hx
    have hsome : (Code.evaln (s - 1) c n).isSome = true := by
      simpa using Option.isSome_iff_exists.mpr ⟨x, hx'⟩
    exact Bool.noConfusion (hsome.symm.trans hs.2)
  omega

/-- Every halting input produces a literal event at its least halting stage. -/
theorem exists_dovetailEvent_of_dom (c : Code) (n : ℕ)
    (hn : n ∈ codeDomain c) :
    ∃ stage, dovetailEvent c (Nat.pair n stage) = true := by
  have hdom : (Code.eval c n).Dom := hn
  obtain ⟨someStage, hsomeStage⟩ :=
    (eval_dom_iff_exists_evaln_isSome c n).1 hdom
  have hex : ∃ stage, (Code.evaln stage c n).isSome = true := by
    exact ⟨someStage, by simpa using hsomeStage⟩
  let stage := Nat.find hex
  have hnow : (Code.evaln stage c n).isSome = true := Nat.find_spec hex
  have hprevious : (Code.evaln (stage - 1) c n).isSome = false := by
    by_contra hne
    have hprev : (Code.evaln (stage - 1) c n).isSome = true :=
      Bool.eq_true_of_not_eq_false hne
    have hpos : 0 < stage := by
      by_contra hz
      have hzero : stage = 0 := by omega
      rw [hzero] at hnow
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (by simpa using hnow)
      have := Code.evaln_bound hx
      omega
    have hlt : stage - 1 < stage := Nat.sub_lt hpos (by omega)
    exact (Nat.find_min hex hlt) hprev
  refine ⟨stage, ?_⟩
  simp [dovetailEvent, firstHaltsAt, hnow, hprevious]

/-- Every emitted event decodes to an input in the program domain. -/
theorem dom_of_dovetailEvent (c : Code) (address : ℕ)
    (h : dovetailEvent c address = true) :
    (Nat.unpair address).1 ∈ codeDomain c := by
  rw [dovetailEvent, firstHaltsAt_eq_true_iff] at h
  exact (eval_dom_iff_exists_evaln_isSome c (Nat.unpair address).1).2
    ⟨(Nat.unpair address).2, by simpa using h.1⟩

/-- On actual event addresses, decoding the input is injective: one input has
only one first-halting stage. -/
theorem unpair_fst_injOn_events (c : Code) :
    Set.InjOn (fun address : ℕ => (Nat.unpair address).1)
      {address | dovetailEvent c address = true} := by
  intro a ha b hb hab
  have hstage : (Nat.unpair a).2 = (Nat.unpair b).2 := by
    apply firstHaltsAt_stage_unique c (Nat.unpair a).1
    · simpa [dovetailEvent] using ha
    · simpa [dovetailEvent, hab] using hb
  apply Nat.pairEquiv.symm.injective
  exact Prod.ext hab hstage

/-- A finite program domain gives only finitely many event addresses. -/
theorem finite_event_addresses_of_finiteDomain (c : Code)
    (hc : FiniteDomain c) :
    Set.Finite {address | dovetailEvent c address = true} := by
  apply Set.Finite.of_finite_image
    (f := fun address : ℕ => (Nat.unpair address).1)
  · apply hc.subset
    rintro n ⟨address, haddress, rfl⟩
    exact dom_of_dovetailEvent c address haddress
  · exact unpair_fst_injOn_events c

/-- Any finite Boolean event set has the canonical final-cut form required by
`FiniteEvents`. -/
theorem finiteEvents_of_finite_true_set (E : StageEvents)
    (hfinite : Set.Finite {address | E.event address = true}) :
    FiniteEvents E := by
  by_cases hempty : {address | E.event address = true} = ∅
  · refine ⟨0, ?_, ?_⟩
    · intro k _
      have hnot : E.event k ≠ true := by
        intro hk
        have : k ∈ ({address | E.event address = true} : Set ℕ) := hk
        rw [hempty] at this
        exact this
      exact Bool.eq_false_of_not_eq_true hnot
    · intro j hj
      omega
  · have hnonempty : ({address | E.event address = true} : Set ℕ).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨last, hlast, hmax⟩ :=
      Set.exists_max_image {address | E.event address = true} id hfinite hnonempty
    refine ⟨last + 1, ?_, ?_⟩
    · intro k hk
      have hnot : E.event k ≠ true := by
        intro htrue
        have hkle : k ≤ last := hmax k htrue
        omega
      exact Bool.eq_false_of_not_eq_true hnot
    · intro j hj
      exact ⟨last, by omega, by omega, hlast⟩

/-- A finite partial-recursive domain produces a canonical finite event cut. -/
theorem finiteDomain_finiteEvents (c : Code) :
    FiniteDomain c → FiniteEvents (codeStageEvents c) := by
  intro hc
  exact finiteEvents_of_finite_true_set (codeStageEvents c)
    (finite_event_addresses_of_finiteDomain c hc)

/-- An infinite partial-recursive domain produces events arbitrarily far out. -/
theorem infiniteDomain_infiniteEvents (c : Code) :
    InfiniteDomain c → InfiniteEvents (codeStageEvents c) := by
  intro hc bound
  obtain ⟨n, hn, hbn⟩ := Set.Infinite.exists_gt hc bound
  obtain ⟨stage, hevent⟩ := exists_dovetailEvent_of_dom c n hn
  refine ⟨Nat.pair n stage, ?_, hevent⟩
  exact le_trans (Nat.le_of_lt hbn) (Nat.left_le_pair n stage)

/-- The two semantic implications needed by the exact literal switch. -/
theorem domain_event_dichotomy (c : Code) :
    (InfiniteDomain c → InfiniteEvents (codeStageEvents c)) ∧
      (FiniteDomain c → FiniteEvents (codeStageEvents c)) :=
  ⟨infiniteDomain_infiniteEvents c, finiteDomain_finiteEvents c⟩

end CodeDovetailStageEvents
end GroupApproximation
