import GroupApproximation.Computability.CodeDovetailStageEvents
import GroupApproximation.Computability.EnumeratedPresentationCodes
import GroupApproximation.Higman.RelatorRE

/-!
# A uniform recursive presentation for the exact event switch

This file turns the code-indexed dovetail stream into concrete recursive
relator syntax.  A natural number selects one of three relator families:
a copied literal relator, an enabled bridge, or an enabled kill relation.
Disabled entries enumerate the empty word, which contributes only the
identity relator.

The enumerator and the symmetric-relator certificate checker are primitive
recursive uniformly in the source partial-recursive code.  Consequently the
group presented by the enumerated relators carries an unconditional
`Higman.RecursivePresentation`.
-/

namespace GroupApproximation
namespace RecursiveSwitchPresentation

open Nat.Partrec
open LiteralNonMFPresentation
open ExactLiteralEFinInfSwitch
open CodeDovetailStageEvents
open Higman

noncomputable section

/-- Explicit numbering of `(stage, literal generator)` by naturals. -/
def copyGeneratorEquivNat : CopyGenerator ≃ ℕ :=
  (Equiv.prodCongr (Equiv.refl ℕ) generatorEquivFin8).trans
    (Nat.divModEquiv 8).symm

@[simp] theorem copyGeneratorEquivNat_apply (stage : ℕ) (g : Generator) :
    copyGeneratorEquivNat (stage, g) = stage * 8 + (generatorEquivFin8 g : ℕ) :=
  rfl

@[simp] theorem copyGeneratorEquivNat_symm_apply (n : ℕ) :
    copyGeneratorEquivNat.symm n =
      (n / 8, generatorEquivFin8.symm (Fin.ofNat 8 n)) :=
  rfl

/-- A fixed literal relator written on the standard eight-letter raw
alphabet. -/
def literalRawWord (r : FreeGroup Generator) : RawWord :=
  r.toWord.map fun p => ((generatorEquivFin8 p.1 : Fin 8), p.2)

/-- The forty-one literal relators as raw words.  This is fixed finite data. -/
def literalRawRelators : List RawWord :=
  relatorList.map literalRawWord

/-- Move a raw eight-letter word into copy `stage`. -/
def copyRaw (stage : ℕ) (w : RawWord) : RawWord :=
  w.map fun p => (stage * 8 + p.1, p.2)

theorem evalRaw_map_index {A : Type} [Group A] (x : ℕ → A)
    (f : ℕ → ℕ) (w : RawWord) :
    evalRaw x (w.map fun p => (f p.1, p.2)) = evalRaw (fun n => x (f n)) w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
      obtain ⟨i, b⟩ := p
      cases b <;> simp [ih]

theorem freeEval_copyRaw (stage : ℕ) (w : RawWord) :
    freeEval (copyRaw stage w) =
      FreeGroup.map (fun i => stage * 8 + i) (freeEval w) := by
  rw [copyRaw, freeEval, evalRaw_map_index]
  symm
  change (FreeGroup.map fun i => stage * 8 + i)
      (evalRaw FreeGroup.of w) = _
  rw [map_evalRaw]
  rfl

theorem freeEval_literalRawWord (r : FreeGroup Generator) :
    freeEval (literalRawWord r) =
      FreeGroup.map (fun g => (generatorEquivFin8 g : ℕ)) r := by
  calc
    freeEval (literalRawWord r) =
        FreeGroup.mk (r.toWord.map fun p =>
          ((generatorEquivFin8 p.1 : ℕ), p.2)) := by
      rw [Higman.freeEval_eq, literalRawWord, List.map_map]
      rfl
    _ = FreeGroup.map (fun g => (generatorEquivFin8 g : ℕ))
        (FreeGroup.mk r.toWord) := by rw [FreeGroup.map.mk]
    _ = FreeGroup.map (fun g => (generatorEquivFin8 g : ℕ)) r := by
      rw [FreeGroup.mk_toWord]

/-- Relabel a word on the stagewise alphabet into the standard countable
alphabet used by the recursive enumerator. -/
def reindexCopyWord : FreeGroup CopyGenerator →* FreeGroup ℕ :=
  FreeGroup.map copyGeneratorEquivNat

theorem freeEval_copied_literal (stage : ℕ) (r : FreeGroup Generator) :
    freeEval (copyRaw stage (literalRawWord r)) =
      reindexCopyWord (copyWord stage r) := by
  rw [freeEval_copyRaw, freeEval_literalRawWord]
  simp only [reindexCopyWord, copyWord]
  rw [FreeGroup.map.comp, FreeGroup.map.comp]
  rfl

/-- The raw bridge word for generator number `g` modulo eight. -/
def bridgeRaw (stage g : ℕ) : RawWord :=
  [(stage * 8 + g % 8, true), ((stage + 1) * 8 + g % 8, false)]

/-- The raw kill word for generator number `g` modulo eight. -/
def killRaw (stage g : ℕ) : RawWord :=
  [(stage * 8 + g % 8, true)]

theorem freeEval_bridgeRaw (stage : ℕ) (g : Generator) :
    freeEval (bridgeRaw stage (generatorEquivFin8 g : ℕ)) =
      reindexCopyWord (bridgeWord stage g) := by
  simp [bridgeRaw, reindexCopyWord, bridgeWord, freeEval,
    Nat.mod_eq_of_lt (generatorEquivFin8 g).isLt]

theorem freeEval_killRaw (stage : ℕ) (g : Generator) :
    freeEval (killRaw stage (generatorEquivFin8 g : ℕ)) =
      reindexCopyWord (killWord stage g) := by
  simp [killRaw, reindexCopyWord, killWord, freeEval,
    Nat.mod_eq_of_lt (generatorEquivFin8 g).isLt]

/-- A total relator enumeration.  The address decodes as
`(family, (stage, argument))`; the family is read modulo three. -/
def rawSwitchRelator (c : Code) (address : ℕ) : RawWord :=
  let outer := Nat.unpair address
  let data := Nat.unpair outer.2
  if outer.1 % 3 = 0 then
    copyRaw data.1 (literalRawRelators.getD data.2 [])
  else if outer.1 % 3 = 1 then
    bif dovetailEvent c data.1 then [] else bridgeRaw data.1 data.2
  else
    bif dovetailEvent c data.1 then killRaw data.1 data.2 else []

theorem primrec_copyRaw : Primrec₂ copyRaw := by
  have hletter : Primrec₂ fun (stage : ℕ) (p : ℕ × Bool) =>
      (stage * 8 + p.1, p.2) := by
    exact (Primrec.pair
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp Primrec.fst (Primrec.const 8))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_map Primrec.snd
    (hletter.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

theorem primrec_bridgeRaw : Primrec₂ bridgeRaw := by
  have hleft : Primrec fun z : ℕ × ℕ => z.1 * 8 + z.2 % 8 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp Primrec.fst (Primrec.const 8))
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 8))
  have hright : Primrec fun z : ℕ × ℕ =>
      (z.1 + 1) * 8 + z.2 % 8 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)) (Primrec.const 8))
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 8))
  exact (Primrec.list_cons.comp
    (Primrec.pair hleft (Primrec.const true))
    (Primrec.list_cons.comp (Primrec.pair hright (Primrec.const false))
      (Primrec.const []))).to₂

theorem primrec_killRaw : Primrec₂ killRaw := by
  have hletter : Primrec fun z : ℕ × ℕ => z.1 * 8 + z.2 % 8 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp Primrec.fst (Primrec.const 8))
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 8))
  exact (Primrec.list_cons.comp
    (Primrec.pair hletter (Primrec.const true)) (Primrec.const [])).to₂

/-- The entire relator enumeration is primitive recursive uniformly in the
source program code. -/
theorem primrec_rawSwitchRelator : Primrec₂ rawSwitchRelator := by
  have hc : Primrec fun z : Code × ℕ => z.1 := Primrec.fst
  have ho : Primrec fun z : Code × ℕ => Nat.unpair z.2 :=
    Primrec.unpair.comp Primrec.snd
  have hfamily : Primrec fun z : Code × ℕ => (Nat.unpair z.2).1 % 3 :=
    Primrec.nat_mod.comp (Primrec.fst.comp ho) (Primrec.const 3)
  have hdata : Primrec fun z : Code × ℕ => Nat.unpair (Nat.unpair z.2).2 :=
    Primrec.unpair.comp (Primrec.snd.comp ho)
  have hj : Primrec fun z : Code × ℕ => (Nat.unpair (Nat.unpair z.2).2).1 :=
    Primrec.fst.comp hdata
  have ha : Primrec fun z : Code × ℕ => (Nat.unpair (Nat.unpair z.2).2).2 :=
    Primrec.snd.comp hdata
  have hfixed : Primrec fun z : Code × ℕ =>
      literalRawRelators.getD (Nat.unpair (Nat.unpair z.2).2).2 [] :=
    Primrec.list_getD ([] : RawWord) |>.comp
      (Primrec.const literalRawRelators) ha
  have hcopy : Primrec fun z : Code × ℕ =>
      copyRaw (Nat.unpair (Nat.unpair z.2).2).1
        (literalRawRelators.getD (Nat.unpair (Nat.unpair z.2).2).2 []) :=
    primrec_copyRaw.comp hj hfixed
  have hevent : Primrec fun z : Code × ℕ =>
      dovetailEvent z.1 (Nat.unpair (Nat.unpair z.2).2).1 :=
    primrec_dovetailEvent.comp hc hj
  have hbridge : Primrec fun z : Code × ℕ =>
      bridgeRaw (Nat.unpair (Nat.unpair z.2).2).1
        (Nat.unpair (Nat.unpair z.2).2).2 :=
    primrec_bridgeRaw.comp hj ha
  have hkill : Primrec fun z : Code × ℕ =>
      killRaw (Nat.unpair (Nat.unpair z.2).2).1
        (Nat.unpair (Nat.unpair z.2).2).2 :=
    primrec_killRaw.comp hj ha
  have hbridgeCase : Primrec fun z : Code × ℕ =>
      bif dovetailEvent z.1 (Nat.unpair (Nat.unpair z.2).2).1 then []
        else bridgeRaw (Nat.unpair (Nat.unpair z.2).2).1
          (Nat.unpair (Nat.unpair z.2).2).2 :=
    Primrec.cond hevent (Primrec.const []) hbridge
  have hkillCase : Primrec fun z : Code × ℕ =>
      bif dovetailEvent z.1 (Nat.unpair (Nat.unpair z.2).2).1 then
        killRaw (Nat.unpair (Nat.unpair z.2).2).1
          (Nat.unpair (Nat.unpair z.2).2).2 else [] :=
    Primrec.cond hevent hkill (Primrec.const [])
  have hzero : PrimrecPred fun z : Code × ℕ =>
      (Nat.unpair z.2).1 % 3 = 0 :=
    Primrec.eq.comp hfamily (Primrec.const 0)
  have hone : PrimrecPred fun z : Code × ℕ =>
      (Nat.unpair z.2).1 % 3 = 1 :=
    Primrec.eq.comp hfamily (Primrec.const 1)
  exact (Primrec.ite hzero hcopy
    (Primrec.ite hone hbridgeCase hkillCase)).of_eq fun _ => rfl

theorem computable_rawSwitchRelator : Computable₂ rawSwitchRelator :=
  primrec_rawSwitchRelator.to_comp

/-! ## A literal s-m-n compiler for the relator enumerator -/

/-- Total decoding of the program component of an uncurried input. -/
def decodeSourceCode (n : ℕ) : Code :=
  (Encodable.decode (α := Code) n).getD Code.zero

theorem primrec_decodeSourceCode : Primrec decodeSourceCode :=
  Primrec.option_getD.comp (@Primrec.decode Code _) (Primrec.const Code.zero)

/-- The uncurried numerical partial function used to obtain one universal
enumerator program.  Its input is literally `Nat.pair (encode c) address`,
the convention used by `Code.curry`. -/
def encodedSwitchEnumerator (input : ℕ) : Part ℕ :=
  Part.some (Encodable.encode
    (rawSwitchRelator (decodeSourceCode (Nat.unpair input).1)
      (Nat.unpair input).2))

theorem encodedSwitchEnumerator_partrec : Nat.Partrec encodedSwitchEnumerator := by
  have hcode : Primrec fun input : ℕ => decodeSourceCode (Nat.unpair input).1 :=
    primrec_decodeSourceCode.comp (Primrec.fst.comp Primrec.unpair)
  have haddress : Primrec fun input : ℕ => (Nat.unpair input).2 :=
    Primrec.snd.comp Primrec.unpair
  have hvalue : Primrec fun input : ℕ => Encodable.encode
      (rawSwitchRelator (decodeSourceCode (Nat.unpair input).1)
        (Nat.unpair input).2) :=
    Primrec.encode.comp (primrec_rawSwitchRelator.comp hcode haddress)
  exact Nat.Partrec.of_primrec (Primrec.nat_iff.mp hvalue)

/-- One fixed program for the two-argument encoded relator enumerator. -/
noncomputable def universalSwitchEnumeratorCode : Code :=
  (Code.exists_code.mp encodedSwitchEnumerator_partrec).choose

theorem eval_universalSwitchEnumeratorCode :
    Code.eval universalSwitchEnumeratorCode = encodedSwitchEnumerator :=
  (Code.exists_code.mp encodedSwitchEnumerator_partrec).choose_spec

/-- Specialize the universal enumerator program at a source program code. -/
noncomputable def switchEnumeratorCode (c : Code) : Code :=
  Code.curry universalSwitchEnumeratorCode (Encodable.encode c)

/-- The s-m-n compiler from source programs to relator-enumerator programs is
computable. -/
theorem computable_switchEnumeratorCode : Computable switchEnumeratorCode :=
  (Code.primrec₂_curry.comp (Primrec.const universalSwitchEnumeratorCode)
    Primrec.encode).to_comp

/-- Exact behavior of the compiled enumerator program. -/
theorem eval_switchEnumeratorCode (c : Code) (address : ℕ) :
    Code.eval (switchEnumeratorCode c) address =
      Part.some (Encodable.encode (rawSwitchRelator c address)) := by
  rw [switchEnumeratorCode, Code.eval_curry, eval_universalSwitchEnumeratorCode]
  simp [encodedSwitchEnumerator, decodeSourceCode]

theorem evaln_zero_eq_none (c : Code) (n : ℕ) :
    Code.evaln 0 c n = Option.none := by
  cases h : Code.evaln 0 c n with
  | none => rfl
  | some y =>
      have hlt : n < 0 := Code.evaln_bound h
      omega

/-- The relator set on the standard countable alphabet. -/
def recursiveSwitchRelators (c : Code) : Set (FreeGroup ℕ) :=
  Set.range fun address => freeEval (rawSwitchRelator c address)

/-- The semantic switch relators, transported along the explicit numbering of
stage-generator pairs. -/
def reindexedSwitchRelators (c : Code) : Set (FreeGroup ℕ) :=
  reindexCopyWord '' switchRelators (codeStageEvents c)

/-- The total raw enumerator names exactly the semantic switch relators; its
disabled and out-of-range addresses contribute only the identity. -/
theorem recursiveSwitchRelators_eq_reindexed (c : Code) :
    recursiveSwitchRelators c = reindexedSwitchRelators c ∪ {1} := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨address, rfl⟩
    generalize houter : Nat.unpair address = outer
    generalize hdata : Nat.unpair outer.2 = data
    by_cases hzero : outer.1 % 3 = 0
    · have hentry : literalRawRelators.getD data.2 [] ∈
          insert [] {w | w ∈ literalRawRelators} := by
        rw [← Set.range_list_getD]
        exact ⟨data.2, rfl⟩
      rcases hentry with hempty | hentry
      · apply Or.inr
        simp only [rawSwitchRelator, houter, hdata, hzero, if_true]
        change freeEval (copyRaw data.1
          (literalRawRelators.getD data.2 [])) = 1
        rw [hempty]
        rfl
      · obtain ⟨r, hr, hrraw⟩ := List.mem_map.mp hentry
        apply Or.inl
        refine ⟨copyWord data.1 r, ?_, ?_⟩
        · exact Or.inl ⟨data.1, r,
            (mem_relators_iff_mem_list r).2 hr, rfl⟩
        · simp only [rawSwitchRelator, houter, hdata, hzero, if_true]
          rw [← hrraw, freeEval_copied_literal]
    · by_cases hone : outer.1 % 3 = 1
      · cases hevent : dovetailEvent c data.1
        · apply Or.inl
          refine ⟨bridgeWord data.1
              (generatorEquivFin8.symm (Fin.ofNat 8 data.2)), ?_, ?_⟩
          · exact Or.inr (Or.inl ⟨data.1,
              generatorEquivFin8.symm (Fin.ofNat 8 data.2), by
                change dovetailEvent c data.1 = false
                exact hevent, rfl⟩)
          · simp only [rawSwitchRelator, houter, hdata, hone, if_true,
              hevent, Bool.cond_false]
            simpa [Fin.ofNat, bridgeRaw, Nat.mod_mod] using
              (freeEval_bridgeRaw data.1
                (generatorEquivFin8.symm (Fin.ofNat 8 data.2))).symm
        · apply Or.inr
          simp [rawSwitchRelator, houter, hdata, hone, hevent, freeEval]
      · cases hevent : dovetailEvent c data.1
        · apply Or.inr
          simp [rawSwitchRelator, houter, hdata, hzero, hone, hevent, freeEval]
        · apply Or.inl
          refine ⟨killWord data.1
              (generatorEquivFin8.symm (Fin.ofNat 8 data.2)), ?_, ?_⟩
          · exact Or.inr (Or.inr ⟨data.1,
              generatorEquivFin8.symm (Fin.ofNat 8 data.2), by
                change dovetailEvent c data.1 = true
                exact hevent, rfl⟩)
          · simp only [rawSwitchRelator, houter, hdata, hzero, hone,
              if_false, hevent, Bool.cond_true]
            simpa [Fin.ofNat, killRaw, Nat.mod_mod] using
              (freeEval_killRaw data.1
                (generatorEquivFin8.symm (Fin.ofNat 8 data.2))).symm
  · rintro x (hx | hx)
    · obtain ⟨r, hr, rfl⟩ := hx
      rcases hr with ⟨stage, s, hs, rfl⟩ | hr
      · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp
          ((mem_relators_iff_mem_list s).1 hs)
        refine ⟨Nat.pair 0 (Nat.pair stage i), ?_⟩
        simp [rawSwitchRelator, literalRawRelators, freeEval_copied_literal]
      · rcases hr with ⟨stage, g, hevent, rfl⟩ |
          ⟨stage, g, hevent, rfl⟩
        · refine ⟨Nat.pair 1
              (Nat.pair stage (generatorEquivFin8 g : ℕ)), ?_⟩
          change dovetailEvent c stage = false at hevent
          simp [rawSwitchRelator, hevent, freeEval_bridgeRaw]
        · refine ⟨Nat.pair 2
              (Nat.pair stage (generatorEquivFin8 g : ℕ)), ?_⟩
          change dovetailEvent c stage = true at hevent
          simp [rawSwitchRelator, hevent, freeEval_killRaw]
    · have hxone : x = 1 := by simpa using hx
      subst x
      refine ⟨Nat.pair 0 (Nat.pair 0 literalRawRelators.length), ?_⟩
      simp [rawSwitchRelator, copyRaw, freeEval]

/-- The group named by the concrete recursive presentation. -/
abbrev RecursiveSwitchGroup (c : Code) : Type :=
  PresentedGroup (recursiveSwitchRelators c)

/-- Reading the compiled program through the repository's standard
enumerated-presentation syntax gives exactly the intended raw relators, plus
the harmless empty-word relator contributed by bounded-evaluator failures. -/
theorem standard_relatorSet_eq (c : Code) :
    EnumeratedPresentationCodes.relatorSet (switchEnumeratorCode c) =
      recursiveSwitchRelators c ∪ {1} := by
  ext x
  constructor
  · rintro ⟨encodedAddress, rfl⟩
    let p := Nat.unpair encodedAddress
    cases heval : Code.evaln p.2 (switchEnumeratorCode c) p.1 with
    | none =>
        apply Or.inr
        simp [EnumeratedPresentationCodes.rawRelator, p, heval, freeEval]
    | some y =>
        have hsound : y ∈ Code.eval (switchEnumeratorCode c) p.1 :=
          Code.evaln_sound heval
        rw [eval_switchEnumeratorCode] at hsound
        have hy : y = Encodable.encode (rawSwitchRelator c p.1) := by
          simpa using hsound
        apply Or.inl
        refine ⟨p.1, ?_⟩
        simp [EnumeratedPresentationCodes.rawRelator,
          EnumeratedPresentationCodes.decodeRawWord, p, heval, hy]
  · rintro (hx | hx)
    · obtain ⟨address, rfl⟩ := hx
      have hmem : Encodable.encode (rawSwitchRelator c address) ∈
          Code.eval (switchEnumeratorCode c) address := by
        rw [eval_switchEnumeratorCode]
        exact Part.mem_some _
      obtain ⟨stage, hstage⟩ := Code.evaln_complete.mp hmem
      have hstage' : Code.evaln stage (switchEnumeratorCode c) address =
          some (Encodable.encode (rawSwitchRelator c address)) := hstage
      refine ⟨Nat.pair address stage, ?_⟩
      simp [EnumeratedPresentationCodes.rawRelator,
        EnumeratedPresentationCodes.decodeRawWord, hstage']
    · have hxone : x = 1 := by simpa using hx
      subst x
      refine ⟨Nat.pair 0 0, ?_⟩
      change freeEval
        ((Code.evaln 0 (switchEnumeratorCode c) 0).map
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

/-- The direct recursive relators and the transported semantic relators have
the same normal closure. -/
theorem normalClosure_recursive_eq_reindexed (c : Code) :
    Subgroup.normalClosure (recursiveSwitchRelators c) =
      Subgroup.normalClosure (reindexedSwitchRelators c) := by
  rw [recursiveSwitchRelators_eq_reindexed, normalClosure_insert_one]

/-- Exact identification of the semantic event-switch group with its concrete
recursive presentation. -/
def switchGroupEquivRecursive (c : Code) :
    SwitchGroup (codeStageEvents c) ≃* RecursiveSwitchGroup c :=
  (PresentedGroup.equivPresentedGroup
      (switchRelators (codeStageEvents c)) copyGeneratorEquivNat).trans
    (QuotientGroup.quotientMulEquivOfEq
      (normalClosure_recursive_eq_reindexed c).symm)

/-- The exact semantic-to-recursive equivalence sends every named stage copy
to its explicitly numbered standard generator. -/
@[simp] theorem switchGroupEquivRecursive_of (c : Code) (stage : ℕ)
    (g : Generator) :
    switchGroupEquivRecursive c
        (PresentedGroup.of (stage, g) : SwitchGroup (codeStageEvents c)) =
      (PresentedGroup.of (copyGeneratorEquivNat (stage, g)) :
        RecursiveSwitchGroup c) := by
  show QuotientGroup.quotientMulEquivOfEq
      (normalClosure_recursive_eq_reindexed c).symm
      (PresentedGroup.equivPresentedGroup
        (switchRelators (codeStageEvents c)) copyGeneratorEquivNat
        (PresentedGroup.of (stage, g))) = _
  rw [PresentedGroup.equivPresentedGroup_apply_of]
  rfl

/-- The standard compiled code and the direct recursive-switch carrier denote
canonically equivalent presented groups. -/
def standardCarrierEquivRecursive (c : Code) :
    EnumeratedPresentationCodes.Carrier (switchEnumeratorCode c) ≃*
      RecursiveSwitchGroup c := by
  have hnormal :
      Subgroup.normalClosure
          (EnumeratedPresentationCodes.relatorSet (switchEnumeratorCode c)) =
        Subgroup.normalClosure (recursiveSwitchRelators c) := by
    rw [standard_relatorSet_eq, normalClosure_insert_one]
  change (FreeGroup ℕ ⧸ Subgroup.normalClosure
      (EnumeratedPresentationCodes.relatorSet (switchEnumeratorCode c))) ≃*
    (FreeGroup ℕ ⧸ Subgroup.normalClosure (recursiveSwitchRelators c))
  exact QuotientGroup.quotientMulEquivOfEq hnormal

/-- End-to-end equivalence from the repository's standard code-indexed
presentation carrier to the original semantic event-switch group. -/
def standardCarrierEquivSwitch (c : Code) :
    EnumeratedPresentationCodes.Carrier (switchEnumeratorCode c) ≃*
      SwitchGroup (codeStageEvents c) :=
  (standardCarrierEquivRecursive c).trans (switchGroupEquivRecursive c).symm

theorem freeEval_append (u v : RawWord) :
    freeEval (u ++ v) = freeEval u * freeEval v :=
  evalRaw_append FreeGroup.of u v

theorem freeEval_invRaw (u : RawWord) :
    freeEval (invRaw u) = (freeEval u)⁻¹ :=
  evalRaw_invRaw FreeGroup.of u

/-- Total decoding of a deletion-certificate list. -/
def decodeSteps (n : ℕ) : List ℕ :=
  (Encodable.decode (α := List ℕ) n).getD []

theorem primrec_decodeSteps : Primrec decodeSteps :=
  Primrec.option_getD.comp (@Primrec.decode (List ℕ) _) (Primrec.const [])

/-- A certificate that `v` represents either an enumerated relator or its
inverse.  The witness decodes as `(relator address, (sign, step-list code))`. -/
def switchRelCheck (c : Code) (v : RawWord) (witness : ℕ) : Bool :=
  let outer := Nat.unpair witness
  let inner := Nat.unpair outer.2
  let target := if inner.1 = 0 then rawSwitchRelator c outer.1
    else invRaw (rawSwitchRelator c outer.1)
  decide (Computability.applySteps (v ++ invRaw target)
    (decodeSteps inner.2) = some [])

/-- The symmetric-relator checker is primitive recursive uniformly in the
source program code. -/
theorem primrec_switchRelCheck :
    Primrec fun z : (Code × RawWord) × ℕ => switchRelCheck z.1.1 z.1.2 z.2 := by
  have hc : Primrec fun z : (Code × RawWord) × ℕ => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hv : Primrec fun z : (Code × RawWord) × ℕ => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have ho : Primrec fun z : (Code × RawWord) × ℕ => Nat.unpair z.2 :=
    Primrec.unpair.comp Primrec.snd
  have hi : Primrec fun z : (Code × RawWord) × ℕ =>
      Nat.unpair (Nat.unpair z.2).2 :=
    Primrec.unpair.comp (Primrec.snd.comp ho)
  have haddress : Primrec fun z : (Code × RawWord) × ℕ =>
      (Nat.unpair z.2).1 := Primrec.fst.comp ho
  have hsign : Primrec fun z : (Code × RawWord) × ℕ =>
      (Nat.unpair (Nat.unpair z.2).2).1 := Primrec.fst.comp hi
  have hsteps : Primrec fun z : (Code × RawWord) × ℕ =>
      decodeSteps (Nat.unpair (Nat.unpair z.2).2).2 :=
    primrec_decodeSteps.comp (Primrec.snd.comp hi)
  have hrel : Primrec fun z : (Code × RawWord) × ℕ =>
      rawSwitchRelator z.1.1 (Nat.unpair z.2).1 :=
    primrec_rawSwitchRelator.comp hc haddress
  have htarget : Primrec fun z : (Code × RawWord) × ℕ =>
      if (Nat.unpair (Nat.unpair z.2).2).1 = 0 then
        rawSwitchRelator z.1.1 (Nat.unpair z.2).1
      else invRaw (rawSwitchRelator z.1.1 (Nat.unpair z.2).1) :=
    Primrec.ite (Primrec.eq.comp hsign (Primrec.const 0)) hrel
      (primrec_invRaw.comp hrel)
  have hword : Primrec fun z : (Code × RawWord) × ℕ =>
      z.1.2 ++ invRaw
        (if (Nat.unpair (Nat.unpair z.2).2).1 = 0 then
          rawSwitchRelator z.1.1 (Nat.unpair z.2).1
        else invRaw (rawSwitchRelator z.1.1 (Nat.unpair z.2).1)) :=
    Primrec.list_append.comp hv (primrec_invRaw.comp htarget)
  exact (Primrec.eq.comp
    (Computability.primrec_applySteps.comp hword hsteps)
    (Primrec.const (some []))).decide.of_eq fun _ => by
      simp only [switchRelCheck]

/-- Exact certificate semantics for the symmetric closure of the enumerated
relator set. -/
theorem freeEval_mem_symmetrize_iff (c : Code) (v : RawWord) :
    freeEval v ∈ symmetrize (recursiveSwitchRelators c) ↔
      ∃ witness, switchRelCheck c v witness = true := by
  constructor
  · rintro (hv | ⟨r, ⟨address, rfl⟩, hrv⟩)
    · obtain ⟨address, haddress⟩ := hv
      obtain ⟨steps, hsteps⟩ := (freeEval_eq_one_iff
        (v ++ invRaw (rawSwitchRelator c address))).1 (by
          rw [freeEval_append, freeEval_invRaw, ← haddress, mul_inv_cancel])
      refine ⟨Nat.pair address (Nat.pair 0 (Encodable.encode steps)), ?_⟩
      simp [switchRelCheck, decodeSteps, hsteps]
    · obtain ⟨steps, hsteps⟩ := (freeEval_eq_one_iff
        (v ++ invRaw (invRaw (rawSwitchRelator c address)))).1 (by
          rw [freeEval_append, freeEval_invRaw, freeEval_invRaw, ← hrv]
          simp)
      refine ⟨Nat.pair address (Nat.pair 1 (Encodable.encode steps)), ?_⟩
      simp [switchRelCheck, decodeSteps, hsteps]
  · rintro ⟨witness, hw⟩
    simp only [switchRelCheck, decide_eq_true_eq] at hw
    let outer := Nat.unpair witness
    let inner := Nat.unpair outer.2
    let target := if inner.1 = 0 then rawSwitchRelator c outer.1
      else invRaw (rawSwitchRelator c outer.1)
    have hone : freeEval (v ++ invRaw target) = 1 :=
      (freeEval_eq_one_iff _).2 ⟨decodeSteps inner.2, hw⟩
    have hone' : freeEval v * (freeEval target)⁻¹ = 1 := by
      simpa only [freeEval_append, freeEval_invRaw] using hone
    have heq : freeEval v = freeEval target := by
      exact mul_inv_eq_one.mp hone'
    by_cases hsign : inner.1 = 0
    · apply Or.inl
      exact ⟨outer.1, by simpa [target, hsign] using heq.symm⟩
    · apply Or.inr
      refine ⟨freeEval (rawSwitchRelator c outer.1), ⟨outer.1, rfl⟩, ?_⟩
      simpa [target, hsign, freeEval_invRaw] using heq.symm

/-- Every code-indexed switch presentation has recursively enumerable word
problem, with the checker above as its only effective input. -/
def recursivePresentation (c : Code) : RecursivePresentation (RecursiveSwitchGroup c) :=
  recursivePresentationPresentedGroup (relCheck := switchRelCheck c)
    (recursiveSwitchRelators c)
    (by
      have h : Primrec fun z : RawWord × ℕ =>
          switchRelCheck c z.1 z.2 :=
        primrec_switchRelCheck.comp
          (Primrec.pair (Primrec.pair (Primrec.const c) Primrec.fst) Primrec.snd)
      exact h.to₂)
    (freeEval_mem_symmetrize_iff c)

end

end RecursiveSwitchPresentation
end GroupApproximation
