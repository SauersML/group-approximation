import GroupApproximation.Computability.CodeDovetailStageEvents
import GroupApproximation.Computability.EnumeratedPresentationCodes
import GroupApproximation.Computability.ParametricFinInfSwitch

/-!
# A uniform recursive switch for an arbitrary finite-presentation seed

This file compiles a finite-presentation code `seed` and a partial-recursive
program `c` into one standard enumerated presentation.  Its event ray has one
copy of `seed` at every stage.  Infinite source domain gives the trivial group;
finite source domain leaves exactly the group presented by `seed`.

Both inputs are genuine compiler inputs.  In particular the output-program
map is jointly computable in `seed` and `c`; no literal negative group is
embedded in the construction.
-/

namespace GroupApproximation
namespace ParametricRecursiveSwitchPresentation

open Nat.Partrec
open PresentationCodes
open ParametricFinInfSwitch
open CodeDovetailStageEvents
open SecondLevelIndexSets
open Higman

noncomputable section

/-- Explicit numbering of `(stage, seed generator)` by naturals. -/
def parametricCopyGeneratorEquivNat (seed : PresentationCode) :
    ParametricCopyGenerator seed ≃ ℕ :=
  (Equiv.prodCongr (Equiv.refl ℕ) (Equiv.refl (Fin (genCount seed)))).trans
    (Nat.divModEquiv (genCount seed)).symm

@[simp] theorem parametricCopyGeneratorEquivNat_apply
    (seed : PresentationCode) (stage : ℕ) (g : SeedGenerator seed) :
    parametricCopyGeneratorEquivNat seed (stage, g) =
      stage * genCount seed + (g : ℕ) :=
  rfl

/-- Relabel the letters of a raw word by the affine total map
`i ↦ base + i % modulus`.

This is the body of `copyRaw` with the presentation code abstracted away.  It
exists so that the `List.map` inside `copyRaw` can be shown primitive recursive
at the carrier `(ℕ × ℕ) × RawWord`, whose encoding is three levels of naturals
and booleans, instead of at `((PresentationCode × ℕ) × RawWord) × (ℕ × Bool)`,
which buries a `List (List (ℕ × Bool))` four levels deep.  `Primrec.list_map`
projects `Primcodable.prim` out of that instance, and reducing it was the
elaboration cost this module used to buy with a heartbeat budget. -/
def shiftLetters (base modulus : ℕ) (w : RawWord) : RawWord :=
  w.map fun p => (base + p.1 % modulus, p.2)

/-- Move a coded seed word into the copy at `stage`.  The modulo is the same
total letter-decoding convention used by `PresentationCodes.wordOf`. -/
def copyRaw (seed : PresentationCode) (stage : ℕ) (w : RawWord) : RawWord :=
  w.map fun p =>
    (stage * genCount seed + p.1 % genCount seed, p.2)

/-- The raw bridge relation at one stage and one total seed-letter code. -/
def bridgeRaw (seed : PresentationCode) (stage g : ℕ) : RawWord :=
  [(stage * genCount seed + g % genCount seed, true),
    ((stage + 1) * genCount seed + g % genCount seed, false)]

/-- The raw kill relation at one stage and one total seed-letter code. -/
def killRaw (seed : PresentationCode) (stage g : ℕ) : RawWord :=
  [(stage * genCount seed + g % genCount seed, true)]

/-- Relabel a semantic stagewise word into the standard countable alphabet. -/
def reindexParametricCopyWord (seed : PresentationCode) :
    FreeGroup (ParametricCopyGenerator seed) →* FreeGroup ℕ :=
  FreeGroup.map (parametricCopyGeneratorEquivNat seed)

theorem freeEval_copyRaw (seed : PresentationCode) (stage : ℕ)
    (w : RawWord) :
    freeEval (copyRaw seed stage w) =
      reindexParametricCopyWord seed
        (copyWord seed stage (wordOf seed w)) := by
  rw [Higman.freeEval_eq]
  simp only [copyRaw, wordOf, reindexParametricCopyWord,
    ParametricFinInfSwitch.copyWord, FreeGroup.map.mk, List.map_map]
  congr 1

theorem freeEval_bridgeRaw (seed : PresentationCode) (stage : ℕ)
    (g : SeedGenerator seed) :
    freeEval (bridgeRaw seed stage (g : ℕ)) =
      reindexParametricCopyWord seed
        (ParametricFinInfSwitch.bridgeWord seed stage g) := by
  simp [bridgeRaw, reindexParametricCopyWord,
    ParametricFinInfSwitch.bridgeWord, freeEval,
    Nat.mod_eq_of_lt g.isLt]

theorem freeEval_killRaw (seed : PresentationCode) (stage : ℕ)
    (g : SeedGenerator seed) :
    freeEval (killRaw seed stage (g : ℕ)) =
      reindexParametricCopyWord seed
        (ParametricFinInfSwitch.killWord seed stage g) := by
  simp [killRaw, reindexParametricCopyWord,
    ParametricFinInfSwitch.killWord, freeEval,
    Nat.mod_eq_of_lt g.isLt]

/-- A total raw relator enumerator, uniform in both the finite seed and the
source program.  Addresses select copied seed relators, bridges, or kills. -/
def rawParametricSwitchRelator (seed : PresentationCode) (c : Code)
    (address : ℕ) : RawWord :=
  let outer := Nat.unpair address
  let data := Nat.unpair outer.2
  if outer.1 % 3 = 0 then
    copyRaw seed data.1 (seed.2.getD data.2 [])
  else if outer.1 % 3 = 1 then
    bif dovetailEvent c data.1 then [] else bridgeRaw seed data.1 data.2
  else
    bif dovetailEvent c data.1 then killRaw seed data.1 data.2 else []

/-! ### The three address fields, named

`Nat.unpair n` is `let s := sqrt n; if n - s * s < s then … else …`, so any
attempt to reduce `(Nat.unpair address).1` has to decide an `ite` whose
condition is stuck on a variable, over a well-founded `Nat.sqrt`.  Every
`Primrec` statement below therefore names its address field instead of
spelling the projection out.  `whnf` will not look through the names on its
own, so a unifier comparing two of these statements has nothing to reduce.
Reducing them is what the heartbeat budget used to pay for. -/

/-- Which of the three relator families an address selects. -/
def addressFamily (address : ℕ) : ℕ := (Nat.unpair address).1 % 3

/-- The stage an address selects. -/
def addressStage (address : ℕ) : ℕ := (Nat.unpair (Nat.unpair address).2).1

/-- The family-specific argument an address carries. -/
def addressArg (address : ℕ) : ℕ := (Nat.unpair (Nat.unpair address).2).2

/-- The enumerator with its two `let`s expanded and its address fields named.

`Primrec.of_eq` below needs the enumerator in exactly this shape.  Asking for
it definitionally, inside the primitive-recursiveness proof, makes `whnf`
reduce `rawParametricSwitchRelator` through both `let`s and the `Nat.unpair`
projections while a `Primrec` unification problem is open.  Here the same
equation is a *rewrite* by the definition's own equation lemma, at a goal with
no `Primcodable` instance in sight, and the proof downstream is a term. -/
theorem rawParametricSwitchRelator_eq (seed : PresentationCode) (c : Code)
    (address : ℕ) :
    rawParametricSwitchRelator seed c address =
      (if addressFamily address = 0 then
        copyRaw seed (addressStage address)
          (seed.2.getD (addressArg address) [])
      else if addressFamily address = 1 then
        (bif dovetailEvent c (addressStage address) then []
          else bridgeRaw seed (addressStage address) (addressArg address))
      else
        (bif dovetailEvent c (addressStage address) then
          killRaw seed (addressStage address) (addressArg address)
        else [])) := by
  simp only [rawParametricSwitchRelator, addressFamily, addressStage,
    addressArg]

/-! ## Joint primitive recursiveness -/

/-- The affine relabelling is primitive recursive.  Proved at the small
carrier: the only list here is the raw word itself. -/
theorem primrec_shiftLetters :
    Primrec fun z : (ℕ × ℕ) × RawWord => shiftLetters z.1.1 z.1.2 z.2 := by
  have hbase : Primrec fun z : ((ℕ × ℕ) × RawWord) × (ℕ × Bool) =>
      z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hmodulus : Primrec fun z : ((ℕ × ℕ) × RawWord) × (ℕ × Bool) =>
      z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hindex : Primrec fun z : ((ℕ × ℕ) × RawWord) × (ℕ × Bool) =>
      z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hletter : Primrec fun z : ((ℕ × ℕ) × RawWord) × (ℕ × Bool) =>
      (z.1.1.1 + z.2.1 % z.1.1.2, z.2.2) :=
    Primrec.pair
      (Primrec.nat_add.comp hbase (Primrec.nat_mod.comp hindex hmodulus))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_map Primrec.snd hletter.to₂).of_eq fun _ => rfl

theorem primrec_copyRaw :
    Primrec fun z : (PresentationCode × ℕ) × RawWord =>
      copyRaw z.1.1 z.1.2 z.2 := by
  have hn : Primrec fun z : (PresentationCode × ℕ) × RawWord =>
      genCount z.1.1 :=
    Primrec.nat_add.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.const 1)
  have hstage : Primrec fun z : (PresentationCode × ℕ) × RawWord =>
      z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hbase : Primrec fun z : (PresentationCode × ℕ) × RawWord =>
      z.1.2 * genCount z.1.1 :=
    Primrec.nat_mul.comp hstage hn
  exact (primrec_shiftLetters.comp
    (Primrec.pair (Primrec.pair hbase hn) Primrec.snd)).of_eq fun _ => rfl

theorem primrec_bridgeRaw :
    Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      bridgeRaw z.1.1 z.1.2 z.2 := by
  have hn : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      genCount z.1.1 :=
    Primrec.nat_add.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.const 1)
  have hstage : Primrec fun z : (PresentationCode × ℕ) × ℕ => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hgmod : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      z.2 % genCount z.1.1 :=
    Primrec.nat_mod.comp Primrec.snd hn
  have hleft : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      z.1.2 * genCount z.1.1 + z.2 % genCount z.1.1 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp hstage hn) hgmod
  have hright : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      (z.1.2 + 1) * genCount z.1.1 + z.2 % genCount z.1.1 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_add.comp hstage (Primrec.const 1)) hn) hgmod
  exact (Primrec.list_cons.comp
    (Primrec.pair hleft (Primrec.const true))
    (Primrec.list_cons.comp (Primrec.pair hright (Primrec.const false))
      (Primrec.const []))).of_eq fun _ => rfl

theorem primrec_killRaw :
    Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      killRaw z.1.1 z.1.2 z.2 := by
  have hn : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      genCount z.1.1 :=
    Primrec.nat_add.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.const 1)
  have hstage : Primrec fun z : (PresentationCode × ℕ) × ℕ => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hindex : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      z.1.2 * genCount z.1.1 + z.2 % genCount z.1.1 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp hstage hn)
      (Primrec.nat_mod.comp Primrec.snd hn)
  exact (Primrec.list_cons.comp
    (Primrec.pair hindex (Primrec.const true)) (Primrec.const [])).of_eq
      fun _ => rfl

/-! ### The address fields and the three branches, one declaration each

Each lemma below elaborates in its own declaration with a two-line context, so
no statement is elaborated twice and a residual cost names the branch it
belongs to. -/

/-- The joint carrier: seed code, source program, relator address. -/
abbrev SwitchInput : Type := (PresentationCode × Code) × ℕ

theorem primrec_addressFamily : Primrec addressFamily :=
  Primrec.nat_mod.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 3)

theorem primrec_addressStage : Primrec addressStage :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

theorem primrec_addressArg : Primrec addressArg :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

theorem primrec_switchSeed : Primrec fun z : SwitchInput => z.1.1 :=
  Primrec.fst.comp Primrec.fst

theorem primrec_switchCode : Primrec fun z : SwitchInput => z.1.2 :=
  Primrec.snd.comp Primrec.fst

theorem primrec_switchFamily :
    Primrec fun z : SwitchInput => addressFamily z.2 :=
  primrec_addressFamily.comp Primrec.snd

theorem primrec_switchStage :
    Primrec fun z : SwitchInput => addressStage z.2 :=
  primrec_addressStage.comp Primrec.snd

theorem primrec_switchArg :
    Primrec fun z : SwitchInput => addressArg z.2 :=
  primrec_addressArg.comp Primrec.snd

theorem primrec_switchEvent :
    Primrec fun z : SwitchInput => dovetailEvent z.1.2 (addressStage z.2) :=
  primrec_dovetailEvent.comp primrec_switchCode primrec_switchStage

/-- The copied-seed-relator branch. -/
theorem primrec_copyBranch :
    Primrec fun z : SwitchInput =>
      copyRaw z.1.1 (addressStage z.2)
        (z.1.1.2.getD (addressArg z.2) []) := by
  have hfixed : Primrec fun z : SwitchInput =>
      z.1.1.2.getD (addressArg z.2) [] :=
    Primrec.list_getD ([] : RawWord) |>.comp
      (Primrec.snd.comp primrec_switchSeed) primrec_switchArg
  exact primrec_copyRaw.comp
    (Primrec.pair (Primrec.pair primrec_switchSeed primrec_switchStage)
      hfixed)

/-- The bridge branch, gated by the dovetail event. -/
theorem primrec_bridgeBranch :
    Primrec fun z : SwitchInput =>
      bif dovetailEvent z.1.2 (addressStage z.2) then []
        else bridgeRaw z.1.1 (addressStage z.2) (addressArg z.2) := by
  have hbridge : Primrec fun z : SwitchInput =>
      bridgeRaw z.1.1 (addressStage z.2) (addressArg z.2) :=
    primrec_bridgeRaw.comp
      (Primrec.pair (Primrec.pair primrec_switchSeed primrec_switchStage)
        primrec_switchArg)
  exact Primrec.cond primrec_switchEvent (Primrec.const []) hbridge

/-- The kill branch, gated by the dovetail event. -/
theorem primrec_killBranch :
    Primrec fun z : SwitchInput =>
      bif dovetailEvent z.1.2 (addressStage z.2) then
        killRaw z.1.1 (addressStage z.2) (addressArg z.2)
      else [] := by
  have hkill : Primrec fun z : SwitchInput =>
      killRaw z.1.1 (addressStage z.2) (addressArg z.2) :=
    primrec_killRaw.comp
      (Primrec.pair (Primrec.pair primrec_switchSeed primrec_switchStage)
        primrec_switchArg)
  exact Primrec.cond primrec_switchEvent hkill (Primrec.const [])

/-- The first family test, stated once so `Primrec.ite` takes it as given. -/
theorem primrecPred_familyZero :
    PrimrecPred fun z : SwitchInput => addressFamily z.2 = 0 :=
  Primrec.eq.comp primrec_switchFamily (Primrec.const 0)

/-- The second family test. -/
theorem primrecPred_familyOne :
    PrimrecPred fun z : SwitchInput => addressFamily z.2 = 1 :=
  Primrec.eq.comp primrec_switchFamily (Primrec.const 1)

/-- The total raw enumerator is primitive recursive jointly in seed, source
program, and relator address.  Two `Primrec.ite`s over the branch lemmas, then
the named unfolding. -/
theorem primrec_rawParametricSwitchRelator :
    Primrec fun z : (PresentationCode × Code) × ℕ =>
      rawParametricSwitchRelator z.1.1 z.1.2 z.2 :=
  (Primrec.ite primrecPred_familyZero primrec_copyBranch
    (Primrec.ite primrecPred_familyOne primrec_bridgeBranch
      primrec_killBranch)).of_eq
    fun z => (rawParametricSwitchRelator_eq z.1.1 z.1.2 z.2).symm

theorem computable_rawParametricSwitchRelator :
    Computable fun z : (PresentationCode × Code) × ℕ =>
      rawParametricSwitchRelator z.1.1 z.1.2 z.2 :=
  primrec_rawParametricSwitchRelator.to_comp

/-! ## A uniform s-m-n compiler -/

/-- Total decoding of the finite seed and source program packed together. -/
def decodeSeedAndSource (n : ℕ) : PresentationCode × Code :=
  (Encodable.decode (α := PresentationCode × Code) n).getD
    ((0, []), Code.zero)

theorem primrec_decodeSeedAndSource : Primrec decodeSeedAndSource :=
  Primrec.option_getD.comp
    (@Primrec.decode (PresentationCode × Code) _)
    (Primrec.const ((0, []), Code.zero))

/-- The uncurried partial function named by one universal enumerator program. -/
def encodedParametricSwitchEnumerator (input : ℕ) : Part ℕ :=
  let parameters := decodeSeedAndSource (Nat.unpair input).1
  Part.some (Encodable.encode
    (rawParametricSwitchRelator parameters.1 parameters.2
      (Nat.unpair input).2))

theorem encodedParametricSwitchEnumerator_partrec :
    Nat.Partrec encodedParametricSwitchEnumerator := by
  have hparameters : Primrec fun input : ℕ =>
      decodeSeedAndSource (Nat.unpair input).1 :=
    primrec_decodeSeedAndSource.comp (Primrec.fst.comp Primrec.unpair)
  have haddress : Primrec fun input : ℕ => (Nat.unpair input).2 :=
    Primrec.snd.comp Primrec.unpair
  have hvalue : Primrec fun input : ℕ => Encodable.encode
      (rawParametricSwitchRelator
        (decodeSeedAndSource (Nat.unpair input).1).1
        (decodeSeedAndSource (Nat.unpair input).1).2
        (Nat.unpair input).2) :=
    Primrec.encode.comp
      (primrec_rawParametricSwitchRelator.comp
        (Primrec.pair hparameters haddress))
  exact Nat.Partrec.of_primrec (Primrec.nat_iff.mp hvalue)

/-- One fixed program for the encoded `(seed, source, address)` enumerator. -/
noncomputable def universalParametricSwitchEnumeratorCode : Code :=
  (Code.exists_code.mp encodedParametricSwitchEnumerator_partrec).choose

theorem eval_universalParametricSwitchEnumeratorCode :
    Code.eval universalParametricSwitchEnumeratorCode =
      encodedParametricSwitchEnumerator :=
  (Code.exists_code.mp encodedParametricSwitchEnumerator_partrec).choose_spec

/-- Compile a finite-presentation seed and a source program into a standard
enumerated-presentation program. -/
noncomputable def parametricSwitchEnumeratorCode
    (seed : PresentationCode) (c : Code) : Code :=
  Code.curry universalParametricSwitchEnumeratorCode
    (Encodable.encode (seed, c))

/-- The compiler is jointly computable in the seed code and source program. -/
theorem computable₂_parametricSwitchEnumeratorCode :
    Computable₂ parametricSwitchEnumeratorCode :=
  (Code.primrec₂_curry.comp
    (Primrec.const universalParametricSwitchEnumeratorCode)
    Primrec.encode).to_comp

theorem eval_parametricSwitchEnumeratorCode (seed : PresentationCode)
    (c : Code) (address : ℕ) :
    Code.eval (parametricSwitchEnumeratorCode seed c) address =
      Part.some (Encodable.encode
        (rawParametricSwitchRelator seed c address)) := by
  rw [parametricSwitchEnumeratorCode, Code.eval_curry,
    eval_universalParametricSwitchEnumeratorCode]
  simp [encodedParametricSwitchEnumerator, decodeSeedAndSource]

theorem evaln_zero_eq_none (seed : PresentationCode) (c : Code) (n : ℕ) :
    Code.evaln 0 (parametricSwitchEnumeratorCode seed c) n = Option.none := by
  cases h : Code.evaln 0 (parametricSwitchEnumeratorCode seed c) n with
  | none => rfl
  | some y =>
      have hlt : n < 0 := Code.evaln_bound h
      omega

/-! ## Exact relator semantics -/

/-- The direct range of the total raw enumerator. -/
def recursiveParametricSwitchRelators (seed : PresentationCode) (c : Code) :
    Set (FreeGroup ℕ) :=
  Set.range fun address => freeEval (rawParametricSwitchRelator seed c address)

/-- The semantic switch relators transported to the standard alphabet. -/
def reindexedParametricSwitchRelators (seed : PresentationCode) (c : Code) :
    Set (FreeGroup ℕ) :=
  reindexParametricCopyWord seed ''
    parametricSwitchRelators seed (codeStageEvents c)

theorem recursiveParametricSwitchRelators_eq_reindexed
    (seed : PresentationCode) (c : Code) :
    recursiveParametricSwitchRelators seed c =
      reindexedParametricSwitchRelators seed c ∪ {1} := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨address, rfl⟩
    generalize houter : Nat.unpair address = outer
    generalize hdata : Nat.unpair outer.2 = data
    by_cases hzero : outer.1 % 3 = 0
    · have hentry : seed.2.getD data.2 [] ∈
          insert [] {w | w ∈ seed.2} := by
        rw [← Set.range_list_getD]
        exact ⟨data.2, rfl⟩
      rcases hentry with hempty | hentry
      · apply Or.inr
        simp only [rawParametricSwitchRelator, houter, hdata, hzero, if_true]
        rw [hempty]
        rfl
      · apply Or.inl
        refine ⟨copyWord seed data.1 (wordOf seed (seed.2.getD data.2 [])), ?_, ?_⟩
        · exact Or.inl ⟨data.1, wordOf seed (seed.2.getD data.2 []), by
            change wordOf seed (seed.2.getD data.2 []) ∈
              (seed.2.map (wordOf seed)).toFinset
            simp only [List.mem_toFinset, List.mem_map]
            exact ⟨seed.2.getD data.2 [], hentry, rfl⟩, rfl⟩
        · simp only [rawParametricSwitchRelator, houter, hdata, hzero, if_true]
          exact (freeEval_copyRaw seed data.1 (seed.2.getD data.2 [])).symm
    · by_cases hone : outer.1 % 3 = 1
      · cases hevent : dovetailEvent c data.1
        · apply Or.inl
          let g : SeedGenerator seed := letterOf seed data.2
          refine ⟨bridgeWord seed data.1 g, ?_, ?_⟩
          · exact Or.inr (Or.inl ⟨data.1, g, by
              change dovetailEvent c data.1 = false
              exact hevent, rfl⟩)
          · simp only [rawParametricSwitchRelator, houter, hdata, hone,
              if_true, hevent, Bool.cond_false]
            simpa [g, letterOf, bridgeRaw, Nat.mod_mod] using
              (freeEval_bridgeRaw seed data.1 g).symm
        · apply Or.inr
          simp [rawParametricSwitchRelator, houter, hdata, hone, hevent,
            freeEval]
      · cases hevent : dovetailEvent c data.1
        · apply Or.inr
          simp [rawParametricSwitchRelator, houter, hdata, hzero, hone,
            hevent, freeEval]
        · apply Or.inl
          let g : SeedGenerator seed := letterOf seed data.2
          refine ⟨killWord seed data.1 g, ?_, ?_⟩
          · exact Or.inr (Or.inr ⟨data.1, g, by
              change dovetailEvent c data.1 = true
              exact hevent, rfl⟩)
          · simp only [rawParametricSwitchRelator, houter, hdata, hzero,
              hone, if_false, hevent, Bool.cond_true]
            simpa [g, letterOf, killRaw, Nat.mod_mod] using
              (freeEval_killRaw seed data.1 g).symm
  · rintro x (hx | hx)
    · obtain ⟨r, hr, rfl⟩ := hx
      rcases hr with ⟨stage, s, hs, rfl⟩ | hr
      · change s ∈ (seed.2.map (wordOf seed)).toFinset at hs
        have hslist : s ∈ seed.2.map (wordOf seed) := by simpa using hs
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hslist
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
        refine ⟨Nat.pair 0 (Nat.pair stage i), ?_⟩
        simp [rawParametricSwitchRelator, freeEval_copyRaw]
      · rcases hr with ⟨stage, g, hevent, rfl⟩ |
          ⟨stage, g, hevent, rfl⟩
        · refine ⟨Nat.pair 1 (Nat.pair stage (g : ℕ)), ?_⟩
          change dovetailEvent c stage = false at hevent
          simp [rawParametricSwitchRelator, hevent,
            freeEval_bridgeRaw]
        · refine ⟨Nat.pair 2 (Nat.pair stage (g : ℕ)), ?_⟩
          change dovetailEvent c stage = true at hevent
          simp [rawParametricSwitchRelator, hevent, freeEval_killRaw]
    · have hxone : x = 1 := by simpa using hx
      subst x
      refine ⟨Nat.pair 0 (Nat.pair 0 seed.2.length), ?_⟩
      simp [rawParametricSwitchRelator, copyRaw, freeEval]

/-- The group named directly by the total parametric raw enumerator. -/
abbrev RecursiveParametricSwitchGroup (seed : PresentationCode) (c : Code) :
    Type :=
  PresentedGroup (recursiveParametricSwitchRelators seed c)

/-- Reading the compiled program through standard enumerated-presentation
syntax recovers the direct relator range, up to the harmless identity. -/
theorem standard_relatorSet_eq (seed : PresentationCode) (c : Code) :
    EnumeratedPresentationCodes.relatorSet
        (parametricSwitchEnumeratorCode seed c) =
      recursiveParametricSwitchRelators seed c ∪ {1} := by
  ext x
  constructor
  · rintro ⟨encodedAddress, rfl⟩
    let p := Nat.unpair encodedAddress
    cases heval : Code.evaln p.2 (parametricSwitchEnumeratorCode seed c) p.1 with
    | none =>
        apply Or.inr
        simp [EnumeratedPresentationCodes.rawRelator, p, heval, freeEval]
    | some y =>
        have hsound : y ∈ Code.eval (parametricSwitchEnumeratorCode seed c) p.1 :=
          Code.evaln_sound heval
        rw [eval_parametricSwitchEnumeratorCode] at hsound
        have hy : y = Encodable.encode
            (rawParametricSwitchRelator seed c p.1) := by
          simpa using hsound
        apply Or.inl
        refine ⟨p.1, ?_⟩
        simp [EnumeratedPresentationCodes.rawRelator,
          EnumeratedPresentationCodes.decodeRawWord, p, heval, hy]
  · rintro (hx | hx)
    · obtain ⟨address, rfl⟩ := hx
      have hmem : Encodable.encode (rawParametricSwitchRelator seed c address) ∈
          Code.eval (parametricSwitchEnumeratorCode seed c) address := by
        rw [eval_parametricSwitchEnumeratorCode]
        exact Part.mem_some _
      obtain ⟨stage, hstage⟩ := Code.evaln_complete.mp hmem
      have hstage' : Code.evaln stage
          (parametricSwitchEnumeratorCode seed c) address =
          some (Encodable.encode (rawParametricSwitchRelator seed c address)) :=
        hstage
      refine ⟨Nat.pair address stage, ?_⟩
      simp [EnumeratedPresentationCodes.rawRelator,
        EnumeratedPresentationCodes.decodeRawWord, hstage']
    · have hxone : x = 1 := by simpa using hx
      subst x
      refine ⟨Nat.pair 0 0, ?_⟩
      change freeEval
        ((Code.evaln 0 (parametricSwitchEnumeratorCode seed c) 0).map
          EnumeratedPresentationCodes.decodeRawWord |>.getD []) = 1
      rw [evaln_zero_eq_none]
      simp [freeEval]

theorem normalClosure_insert_one (S : Set (FreeGroup ℕ)) :
    Subgroup.normalClosure (S ∪ {1}) = Subgroup.normalClosure S := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x (hx | hx)
    · exact Subgroup.subset_normalClosure hx
    · have : x = 1 := by simpa using hx
      subst x
      exact Subgroup.one_mem _
  · exact Subgroup.normalClosure_mono Set.subset_union_left

theorem normalClosure_recursive_eq_reindexed
    (seed : PresentationCode) (c : Code) :
    Subgroup.normalClosure (recursiveParametricSwitchRelators seed c) =
      Subgroup.normalClosure (reindexedParametricSwitchRelators seed c) := by
  rw [recursiveParametricSwitchRelators_eq_reindexed,
    normalClosure_insert_one]

/-- Exact semantic-to-direct-recursive identification. -/
def parametricSwitchGroupEquivRecursive (seed : PresentationCode) (c : Code) :
    ParametricSwitchGroup seed (codeStageEvents c) ≃*
      RecursiveParametricSwitchGroup seed c :=
  (PresentedGroup.equivPresentedGroup
      (parametricSwitchRelators seed (codeStageEvents c))
      (parametricCopyGeneratorEquivNat seed)).trans
    (QuotientGroup.quotientMulEquivOfEq
      (normalClosure_recursive_eq_reindexed seed c).symm)

@[simp] theorem parametricSwitchGroupEquivRecursive_of
    (seed : PresentationCode) (c : Code) (stage : ℕ)
    (g : SeedGenerator seed) :
    parametricSwitchGroupEquivRecursive seed c
        (PresentedGroup.of (stage, g) :
          ParametricSwitchGroup seed (codeStageEvents c)) =
      (PresentedGroup.of
        (parametricCopyGeneratorEquivNat seed (stage, g)) :
          RecursiveParametricSwitchGroup seed c) := by
  show QuotientGroup.quotientMulEquivOfEq
      (normalClosure_recursive_eq_reindexed seed c).symm
      (PresentedGroup.equivPresentedGroup
        (parametricSwitchRelators seed (codeStageEvents c))
        (parametricCopyGeneratorEquivNat seed)
        (PresentedGroup.of (stage, g))) = _
  rw [PresentedGroup.equivPresentedGroup_apply_of]
  rfl

/-- The standard compiled carrier is canonically equivalent to the direct
recursive-switch carrier. -/
def standardCarrierEquivRecursive (seed : PresentationCode) (c : Code) :
    EnumeratedPresentationCodes.Carrier
        (parametricSwitchEnumeratorCode seed c) ≃*
      RecursiveParametricSwitchGroup seed c := by
  have hnormal :
      Subgroup.normalClosure
          (EnumeratedPresentationCodes.relatorSet
            (parametricSwitchEnumeratorCode seed c)) =
        Subgroup.normalClosure (recursiveParametricSwitchRelators seed c) := by
    rw [standard_relatorSet_eq, normalClosure_insert_one]
  change (FreeGroup ℕ ⧸ Subgroup.normalClosure
      (EnumeratedPresentationCodes.relatorSet
        (parametricSwitchEnumeratorCode seed c))) ≃*
    (FreeGroup ℕ ⧸ Subgroup.normalClosure
      (recursiveParametricSwitchRelators seed c))
  exact QuotientGroup.quotientMulEquivOfEq hnormal

/-- End-to-end equivalence from standard code syntax to the semantic
seed-parametric event switch. -/
def standardCarrierEquivParametricSwitch
    (seed : PresentationCode) (c : Code) :
    EnumeratedPresentationCodes.Carrier
        (parametricSwitchEnumeratorCode seed c) ≃*
      ParametricSwitchGroup seed (codeStageEvents c) :=
  (standardCarrierEquivRecursive seed c).trans
    (parametricSwitchGroupEquivRecursive seed c).symm

/-! ## Exact branch endpoints on standard syntax -/

/-- The carrier emitted by the jointly parametric compiler. -/
abbrev ParametricCompiledCarrier (seed : PresentationCode) (c : Code) : Type :=
  EnumeratedPresentationCodes.Carrier
    (parametricSwitchEnumeratorCode seed c)

/-- Infinite source domain makes the standard compiled carrier trivial. -/
theorem compiledCarrier_subsingleton_of_infiniteDomain
    (seed : PresentationCode) (c : Code) (hc : InfiniteDomain c) :
    Subsingleton (ParametricCompiledCarrier seed c) := by
  let e := standardCarrierEquivParametricSwitch seed c
  letI : Subsingleton (ParametricSwitchGroup seed (codeStageEvents c)) :=
    subsingleton_of_infiniteEvents seed _
      (infiniteDomain_infiniteEvents c hc)
  exact ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩

/-- Infinite source domain gives an explicit equivalence with `PUnit`. -/
theorem compiledCarrier_equiv_punit_of_infiniteDomain
    (seed : PresentationCode) (c : Code) (hc : InfiniteDomain c) :
    Nonempty (ParametricCompiledCarrier seed c ≃* PUnit) := by
  exact ⟨(standardCarrierEquivParametricSwitch seed c).trans
    (equivPUnitOfInfiniteEvents seed _
      (infiniteDomain_infiniteEvents c hc))⟩

/-- Finite source domain leaves exactly the group presented by `seed`. -/
theorem compiledCarrier_equiv_seed_of_finiteDomain
    (seed : PresentationCode) (c : Code) (hc : FiniteDomain c) :
    Nonempty (ParametricCompiledCarrier seed c ≃* Carrier seed) := by
  obtain ⟨e⟩ := nonempty_equiv_seed_of_finiteEvents seed
    (codeStageEvents c) (finiteDomain_finiteEvents c hc)
  exact ⟨(standardCarrierEquivParametricSwitch seed c).trans e⟩

/-- Every compiled carrier has exactly one of the two advertised branch
types: the trivial group or the arbitrary finite-presentation seed. -/
theorem compiled_two_isomorphism_types (seed : PresentationCode) (c : Code) :
    (InfiniteDomain c ∧
        Nonempty (ParametricCompiledCarrier seed c ≃* PUnit)) ∨
      (FiniteDomain c ∧
        Nonempty (ParametricCompiledCarrier seed c ≃* Carrier seed)) := by
  by_cases hc : InfiniteDomain c
  · exact Or.inl
      ⟨hc, compiledCarrier_equiv_punit_of_infiniteDomain seed c hc⟩
  · have hfinite : FiniteDomain c := by
      simpa only [FiniteDomain, InfiniteDomain, Set.not_infinite] using hc
    exact Or.inr
      ⟨hfinite, compiledCarrier_equiv_seed_of_finiteDomain seed c hfinite⟩

end

end ParametricRecursiveSwitchPresentation
end GroupApproximation
