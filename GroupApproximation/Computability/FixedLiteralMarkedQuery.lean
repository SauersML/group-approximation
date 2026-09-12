import GroupApproximation.Computability.CodedMicrostate
import GroupApproximation.Computability.FixedMarkedQueryHierarchy
import GroupApproximation.Computability.SeededSelfAwareMFCompiler
import GroupApproximation.Higman.BlockWordProblem
import GroupApproximation.Sofic.LiteralNonMFEndpoint

/-!
# The concrete fixed literal non-MF marked query

This file instantiates `FixedMarkedQueryHierarchy.EffectiveQuery` with the
literal eight-generator, forty-one-relator group `E`.  A witness consists of
eight target words and one checked normal-closure certificate for each source
relator.  A challenge is a checked normal-closure certificate killing the
image of the fixed marked involution.

The checker is executable raw-list surgery.  Its semantic theorem is exact:
it survives on a finite presentation code `c` precisely when there is a
homomorphism from the literal group to `PresentationCodes.Carrier c` whose
image of the literal mark is nontrivial.  Consequently every surviving target
is non-MF, by functoriality of the already proved MF-invisibility of the mark.
-/

namespace GroupApproximation
namespace FixedLiteralMarkedQuery

open PresentationCodes AdianRabinWordProblem WordProblemRE
open FixedMarkedQueryHierarchy
open LiteralNonMFPresentation

abbrev RawWord := List (ℕ × Bool)

/-- Eight target words, in the literal ordering `v₁,v₂,v₃,x,y,z,t,c`. -/
abbrev Assignment := List.Vector RawWord 8

/-- One checked target word-problem certificate for each of the forty-one
literal source relators. -/
abbrev RelatorCertificates := List.Vector SearchData 41

/-- The existential witness decoded from one natural number. -/
abbrev WitnessData := Assignment × RelatorCertificates

/-- Total conversion of a natural index to the fixed eight-letter alphabet. -/
def fin8 (n : ℕ) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

/-- Total conversion of a natural index to the fixed relator packet. -/
def fin41 (n : ℕ) : Fin 41 := ⟨n % 41, Nat.mod_lt _ (by decide)⟩

/-- A source free-group word written as raw indices in the printed
eight-letter ordering. -/
noncomputable def sourceRaw (w : FreeGroup Generator) : RawWord :=
  w.toWord.map fun p => ((generatorEquivFin8 p.1 : Fin 8).val, p.2)

/-- The `i`-th literal relator, using the proved length `41` of the displayed
relator list. -/
noncomputable def sourceRelator (i : Fin 41) : FreeGroup Generator :=
  relatorList.get (Fin.cast relatorList_length.symm i)

/-- The raw spelling of the `i`-th literal relator. -/
noncomputable def sourceRelatorRaw (i : Fin 41) : RawWord :=
  sourceRaw (sourceRelator i)

/-- The raw spelling of the fixed literal marked word. -/
noncomputable def sourceMarkRaw : RawWord := sourceRaw markedWord

/-- Substitute eight target words into a raw source word.  Out-of-range source
indices are totalized modulo eight; the source packet itself only uses indices
below eight. -/
def substitute (a : Assignment) (w : RawWord) : RawWord :=
  (w.map fun p => bif p.2 then a.get (fin8 p.1)
    else RawWord.invWord (a.get (fin8 p.1))).flatten

theorem primrec_fin8 : Primrec fin8 := by
  apply Primrec.fin_val_iff.mp
  exact Primrec.nat_mod.comp Primrec.id (Primrec.const 8)

theorem primrec_fin41 : Primrec fin41 := by
  apply Primrec.fin_val_iff.mp
  exact Primrec.nat_mod.comp Primrec.id (Primrec.const 41)

/-- Raw substitution is primitive recursive. -/
theorem primrec_substitute : Primrec₂ substitute := by
  have hletter : Primrec fun z : Assignment × (ℕ × Bool) =>
      bif z.2.2 then z.1.get (fin8 z.2.1)
        else RawWord.invWord (z.1.get (fin8 z.2.1)) := by
    have happ : Primrec fun z : Assignment × (ℕ × Bool) =>
        z.1.get (fin8 z.2.1) :=
      Primrec.vector_get.comp Primrec.fst
        (primrec_fin8.comp (Primrec.fst.comp Primrec.snd))
    exact Primrec.cond (Primrec.snd.comp Primrec.snd) happ
      (RawTransformPrimrec.primrec_invWord.comp happ)
  exact (Primrec.list_flatten.comp
    (Primrec.list_map Primrec.snd
      (hletter.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂)).of_eq
        fun _ => rfl

/-- The fixed relator table is primitive recursive because its domain is
finite.  No execution of the noncomputable free-group presentation is used. -/
theorem primrec_sourceRelatorRaw : Primrec sourceRelatorRaw :=
  Primrec.dom_finite sourceRelatorRaw

/-- The target word and certificate check for one literal source relator. -/
noncomputable def relatorCheck
    (x : PresentationCode × WitnessData) (i : Fin 41) : Bool :=
  searchCheck (x.1, substitute x.2.1 (sourceRelatorRaw i)) (x.2.2.get i)

theorem primrec_relatorCheck : Primrec₂ relatorCheck := by
  have hc : Primrec fun z : (PresentationCode × WitnessData) × Fin 41 => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec fun z : (PresentationCode × WitnessData) × Fin 41 => z.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hw : Primrec fun z : (PresentationCode × WitnessData) × Fin 41 =>
      substitute z.1.2.1 (sourceRelatorRaw z.2) :=
    primrec_substitute.comp ha (primrec_sourceRelatorRaw.comp Primrec.snd)
  have hp : Primrec fun z : (PresentationCode × WitnessData) × Fin 41 =>
      z.1.2.2.get z.2 :=
    Primrec.vector_get.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  exact primrec_searchCheck.comp (Primrec.pair hc hw) hp

/-- All forty-one source relators have valid target certificates. -/
noncomputable def relatorsValid (x : PresentationCode × WitnessData) : Prop :=
  ∀ i : Fin 41, relatorCheck x i = true

noncomputable instance relatorsValid_decidable
    (x : PresentationCode × WitnessData) : Decidable (relatorsValid x) :=
  Classical.dec _

/-- Boolean form of the finite source-relator verification. -/
noncomputable def relatorsValidCheck (x : PresentationCode × WitnessData) : Bool :=
  decide (relatorsValid x)

theorem relatorsValidCheck_eq_true_iff (x : PresentationCode × WitnessData) :
    relatorsValidCheck x = true ↔ relatorsValid x :=
  decide_eq_true_iff

theorem primrec_relatorsValidCheck : Primrec relatorsValidCheck := by
  have hall : Primrec fun x : PresentationCode × WitnessData =>
      fun i : Fin 41 => relatorCheck x i :=
    Primrec.fin_curry.mpr primrec_relatorCheck
  have hp : PrimrecPred fun x : PresentationCode × WitnessData =>
      (fun i : Fin 41 => relatorCheck x i) = fun _ => true :=
    Primrec.eq.comp hall (Primrec.const fun _ : Fin 41 => true)
  exact hp.decide.of_eq fun x => by
    unfold relatorsValidCheck relatorsValid
    exact decide_eq_decide.mpr funext_iff

/-- Check one decoded witness against one numerical challenge. -/
noncomputable def witnessFailure
    (z : ((PresentationCode × ℕ) × ℕ) × WitnessData) : Bool :=
  bif relatorsValidCheck (z.1.1.1, z.2) then
    (Encodable.decode (α := SearchData) z.1.2).map
      (fun cert => searchCheck
        (z.1.1.1, substitute z.2.1 sourceMarkRaw) cert) |>.getD false
  else true

/-- The concrete failure checker.  Malformed existential witnesses fail
immediately.  Once all source relators are certified, a challenge succeeds
exactly when it certifies triviality of the substituted marked word. -/
noncomputable def failureCheck
    (x : PresentationCode × ℕ) (derivation : ℕ) : Bool :=
  (Encodable.decode (α := WitnessData) x.2).map
    (fun witness => witnessFailure ((x, derivation), witness)) |>.getD true

/-- The concrete failure checker is computable. -/
theorem computable_failureCheck : Computable₂ failureCheck := by
  have h : Primrec fun z : (PresentationCode × ℕ) × ℕ => failureCheck z.1 z.2 := by
    have hwit : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
        Encodable.decode (α := WitnessData) z.1.2 :=
      Primrec.decode.comp (Primrec.snd.comp Primrec.fst)
    have hsome : Primrec witnessFailure := by
      have hc : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          z.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
      have ha : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          z.2.1 := Primrec.fst.comp Primrec.snd
      have hvalid : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          relatorsValidCheck (z.1.1.1, z.2) :=
        primrec_relatorsValidCheck.comp (Primrec.pair hc Primrec.snd)
      have hderiv : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          Encodable.decode (α := SearchData) z.1.2 :=
        Primrec.decode.comp (Primrec.snd.comp Primrec.fst)
      have hword : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          substitute z.2.1 sourceMarkRaw :=
        primrec_substitute.comp ha (Primrec.const sourceMarkRaw)
      have hsearch : Primrec₂ fun
          (z : ((PresentationCode × ℕ) × ℕ) × WitnessData) (cert : SearchData) =>
            searchCheck (z.1.1.1, substitute z.2.1 sourceMarkRaw) cert :=
        primrec_searchCheck.comp
          (Primrec.pair (hc.comp Primrec.fst) (hword.comp Primrec.fst)) Primrec.snd
      have hmapped : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          (Encodable.decode (α := SearchData) z.1.2).map
            (fun cert => searchCheck
              (z.1.1.1, substitute z.2.1 sourceMarkRaw) cert) :=
        Primrec.option_map hderiv hsearch
      have hchallenge : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          ((Encodable.decode (α := SearchData) z.1.2).map
            (fun cert => searchCheck
              (z.1.1.1, substitute z.2.1 sourceMarkRaw) cert)).getD false :=
        Primrec.option_getD.comp hmapped (Primrec.const false)
      exact Primrec.cond hvalid hchallenge (Primrec.const true)
    have hmapped : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
        (Encodable.decode (α := WitnessData) z.1.2).map
          (fun witness => witnessFailure (z, witness)) :=
      Primrec.option_map hwit hsome
    exact Primrec.option_getD.comp hmapped (Primrec.const true)
  exact h.to_comp.to₂

/-- The literal eight-generator marked query. -/
noncomputable def literalQuery : EffectiveQuery PresentationCode where
  failureCheck := failureCheck
  failureCheck_computable := computable_failureCheck

/-! ## Exact semantics of raw substitution -/

theorem generatorEquivFin8_symm_fin8_val (g : Generator) :
    generatorEquivFin8.symm (fin8 (generatorEquivFin8 g).val) = g := by
  apply generatorEquivFin8.injective
  simp [fin8, Nat.mod_eq_of_lt (generatorEquivFin8 g).isLt]

/-- Substitution followed by target evaluation is raw-word evaluation at the
eight assigned target elements. -/
theorem ev_substitute (c : PresentationCode) (a : Assignment) (w : RawWord) :
    MFMicrostate.ev c (substitute a w) =
      Higman.evalRaw (fun n ↦ MFMicrostate.ev c (a.get (fin8 n))) w := by
  induction w with
  | nil => simp [substitute]
  | cons p w ih =>
      obtain ⟨n, b⟩ := p
      cases b with
      | false =>
          change MFMicrostate.ev c
              (RawWord.invWord (a.get (fin8 n)) ++ substitute a w) =
            (MFMicrostate.ev c (a.get (fin8 n)))⁻¹ *
              Higman.evalRaw
                (fun k ↦ MFMicrostate.ev c (a.get (fin8 k))) w
          rw [MFMicrostate.ev_append, MFMicrostate.ev_invWord, ih]
      | true =>
          change MFMicrostate.ev c (a.get (fin8 n) ++ substitute a w) =
            MFMicrostate.ev c (a.get (fin8 n)) *
              Higman.evalRaw
                (fun k ↦ MFMicrostate.ev c (a.get (fin8 k))) w
          rw [MFMicrostate.ev_append, ih]

/-- The raw spelling of a literal source word evaluates exactly as that free
word. -/
theorem evalRaw_sourceRaw {M : Type} [Group M]
    (f : Generator → M) (w : FreeGroup Generator) :
    (@Higman.evalRaw M _
        (fun n : ℕ ↦ f (generatorEquivFin8.symm (fin8 n))) (sourceRaw w)) =
      FreeGroup.lift f w := by
  have hmap :
      FreeGroup.lift f
          (Higman.evalRaw
            (fun n ↦ FreeGroup.of (generatorEquivFin8.symm (fin8 n)))
            (sourceRaw w)) =
        Higman.evalRaw
          (fun n ↦ f (generatorEquivFin8.symm (fin8 n))) (sourceRaw w) := by
    rw [Higman.map_evalRaw]
    simp
  rw [← hmap]
  rw [Higman.evalRaw_freeGroup]
  have hletters :
      (sourceRaw w).map
          (fun p ↦ (generatorEquivFin8.symm (fin8 p.1), p.2)) =
        w.toWord := by
    simp only [sourceRaw, List.map_map]
    calc
      List.map
          ((fun p ↦ (generatorEquivFin8.symm (fin8 p.1), p.2)) ∘
            fun p ↦ ((generatorEquivFin8 p.1).val, p.2)) w.toWord =
          List.map id w.toWord := by
            apply List.map_congr_left
            rintro ⟨g, b⟩ hg
            change (generatorEquivFin8.symm
              (fin8 (generatorEquivFin8 g).val), b) = (g, b)
            rw [generatorEquivFin8_symm_fin8_val]
      _ = w.toWord := List.map_id _
  rw [hletters, FreeGroup.mk_toWord]

/-- The concrete target value of a substituted literal word. -/
theorem ev_substitute_sourceRaw (c : PresentationCode) (a : Assignment)
    (w : FreeGroup Generator) :
    MFMicrostate.ev c (substitute a (sourceRaw w)) =
      FreeGroup.lift
        (fun g ↦ MFMicrostate.ev c (a.get (generatorEquivFin8 g))) w := by
  rw [ev_substitute]
  simpa using evalRaw_sourceRaw
    (f := fun g ↦ MFMicrostate.ev c (a.get (generatorEquivFin8 g))) w

theorem sourceRelator_mem (i : Fin 41) : sourceRelator i ∈ relators := by
  rw [mem_relators_iff_mem_list]
  exact List.get_mem _ _

theorem exists_sourceRelator_eq {r : FreeGroup Generator} (hr : r ∈ relators) :
    ∃ i : Fin 41, sourceRelator i = r := by
  rw [mem_relators_iff_mem_list] at hr
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
  refine ⟨Fin.cast relatorList_length i, ?_⟩
  simpa [sourceRelator] using hi

/-! ## The checker recognizes exactly the concrete marked-word condition -/

/-- A tuple of eight target words kills every literal relator but retains the
literal marked word. -/
def ConcreteSurvives (c : PresentationCode) : Prop :=
  ∃ a : Assignment,
    (∀ i : Fin 41, WordProblem c (substitute a (sourceRelatorRaw i))) ∧
      ¬ WordProblem c (substitute a sourceMarkRaw)

theorem survives_iff_concrete (c : PresentationCode) :
    Survives literalQuery c ↔ ConcreteSurvives c := by
  constructor
  · rintro ⟨witnessCode, hall⟩
    cases hwitness : Encodable.decode (α := WitnessData) witnessCode with
    | none =>
        have h := hall 0
        simp [literalQuery, failureCheck, hwitness] at h
    | some witness =>
        rcases witness with ⟨a, certificates⟩
        have hvalidCheck :
            relatorsValidCheck (c, (a, certificates)) = true := by
          cases hv : relatorsValidCheck (c, (a, certificates)) with
          | false =>
              have h := hall 0
              simp [literalQuery, failureCheck, hwitness, witnessFailure, hv] at h
          | true => rfl
        have hvalid : relatorsValid (c, (a, certificates)) :=
          (relatorsValidCheck_eq_true_iff _).1 hvalidCheck
        refine ⟨a, ?_, ?_⟩
        · intro i
          have hcheck := hvalid i
          exact (wordProblemPred_iff_exists
            (c, substitute a (sourceRelatorRaw i))).2
              ⟨certificates.get i, hcheck⟩
        · intro hmark
          obtain ⟨cert, hcert⟩ := (wordProblemPred_iff_exists
            (c, substitute a sourceMarkRaw)).1 hmark
          have h := hall (Encodable.encode cert)
          simp [literalQuery, failureCheck, hwitness, witnessFailure,
            hvalidCheck, Encodable.encodek, hcert] at h
  · rintro ⟨a, hrel, hmark⟩
    have hexists : ∀ i : Fin 41, ∃ cert : SearchData,
        searchCheck (c, substitute a (sourceRelatorRaw i)) cert = true := by
      intro i
      exact (wordProblemPred_iff_exists
        (c, substitute a (sourceRelatorRaw i))).1 (hrel i)
    let certificates : RelatorCertificates :=
      List.Vector.ofFn fun i ↦ Classical.choose (hexists i)
    have hcertificates : relatorsValid (c, (a, certificates)) := by
      intro i
      simpa [relatorCheck, certificates] using Classical.choose_spec (hexists i)
    have hvalidCheck : relatorsValidCheck (c, (a, certificates)) = true :=
      (relatorsValidCheck_eq_true_iff _).2 hcertificates
    refine ⟨Encodable.encode (a, certificates), ?_⟩
    intro derivation
    cases hderivation : Encodable.decode (α := SearchData) derivation with
    | none =>
        simp [literalQuery, failureCheck, witnessFailure,
          Encodable.encodek, hvalidCheck, hderivation]
    | some cert =>
        have hsearch : searchCheck (c, substitute a sourceMarkRaw) cert = false := by
          cases hs : searchCheck (c, substitute a sourceMarkRaw) cert with
          | false => rfl
          | true =>
              exfalso
              apply hmark
              exact (wordProblemPred_iff_exists
                (c, substitute a sourceMarkRaw)).2 ⟨cert, hs⟩
        simp [literalQuery, failureCheck, witnessFailure,
          Encodable.encodek, hvalidCheck, hderivation, hsearch]

/-! ## Exact homomorphism semantics and the non-MF consequence -/

/-- The literal marked group has a homomorphic image in the coded target that
retains the fixed literal mark. -/
def HomSurvives (c : PresentationCode) : Prop :=
  ∃ φ : MarkedGroup →* Carrier c, φ mark ≠ 1

theorem hom_wordInMarkedGroup (c : PresentationCode)
    (φ : MarkedGroup →* Carrier c) (w : FreeGroup Generator) :
    φ (wordInMarkedGroup w) =
      FreeGroup.lift (fun g ↦ φ (PresentedGroup.of g)) w := by
  refine freeGroup_hom_eq_on_generators
    (f := φ.comp wordInMarkedGroup)
    (g := FreeGroup.lift (fun g ↦ φ (PresentedGroup.of g))) ?_ w
  intro g
  rw [MonoidHom.comp_apply,
    show wordInMarkedGroup (FreeGroup.of g) = PresentedGroup.of g from rfl,
    FreeGroup.lift_apply_of]

theorem concrete_iff_homSurvives (c : PresentationCode) :
    ConcreteSurvives c ↔ HomSurvives c := by
  constructor
  · rintro ⟨a, hrel, hmark⟩
    let f : Generator → Carrier c :=
      fun g ↦ MFMicrostate.ev c (a.get (generatorEquivFin8 g))
    have hkills : ∀ r ∈ relators, FreeGroup.lift f r = 1 := by
      intro r hr
      obtain ⟨i, hi⟩ := exists_sourceRelator_eq hr
      subst r
      have hev := (MFMicrostate.ev_eq_one_iff
        c (substitute a (sourceRelatorRaw i))).2 (hrel i)
      simpa [f, sourceRelatorRaw, ev_substitute_sourceRaw] using hev
    let φ : MarkedGroup →* Carrier c := PresentedGroup.toGroup hkills
    refine ⟨φ, ?_⟩
    intro htrivial
    apply hmark
    apply (MFMicrostate.ev_eq_one_iff c (substitute a sourceMarkRaw)).1
    simpa [φ, f, sourceMarkRaw, ev_substitute_sourceRaw,
      presentedToGroup_mk] using htrivial
  · rintro ⟨φ, hφ⟩
    let a : Assignment := List.Vector.ofFn fun i ↦
      Classical.choose
        (MFMicrostate.ev_surjective c
          (φ (PresentedGroup.of (generatorEquivFin8.symm i))))
    have ha (i : Fin 8) :
        MFMicrostate.ev c (a.get i) =
          φ (PresentedGroup.of (generatorEquivFin8.symm i)) := by
      simpa [a] using Classical.choose_spec
        (MFMicrostate.ev_surjective c
          (φ (PresentedGroup.of (generatorEquivFin8.symm i))))
    have hgen (g : Generator) :
        MFMicrostate.ev c (a.get (generatorEquivFin8 g)) =
          φ (PresentedGroup.of g) := by
      simpa using ha (generatorEquivFin8 g)
    refine ⟨a, ?_, ?_⟩
    · intro i
      apply (MFMicrostate.ev_eq_one_iff
        c (substitute a (sourceRelatorRaw i))).1
      rw [sourceRelatorRaw, ev_substitute_sourceRaw]
      simp only [hgen]
      rw [← hom_wordInMarkedGroup c φ]
      rw [PresentedGroup.one_of_mem (sourceRelator_mem i), map_one]
    · intro hmark
      have hev := (MFMicrostate.ev_eq_one_iff
        c (substitute a sourceMarkRaw)).2 hmark
      rw [sourceMarkRaw, ev_substitute_sourceRaw] at hev
      simp only [hgen] at hev
      rw [← hom_wordInMarkedGroup c φ] at hev
      exact hφ hev

/-- The executable query has exactly the intended marked-homomorphism
semantics. -/
theorem survives_iff_homSurvives (c : PresentationCode) :
    Survives literalQuery c ↔ HomSurvives c :=
  (survives_iff_concrete c).trans (concrete_iff_homSurvives c)

/-- Every target on which the literal query survives is non-MF. -/
theorem not_isOperatorMF_of_survives (c : PresentationCode)
    (h : Survives literalQuery c) :
    ¬ IsOperatorMF (Carrier c) := by
  obtain ⟨φ, hφ⟩ := (survives_iff_homSurvives c).1 h
  exact SeededSelfAwareMFCompiler.quotient_not_isOperatorMF_of_invisible_mark_survives
    LiteralNonMFEndpoint.literal_mark_normMFInvisible φ hφ

end FixedLiteralMarkedQuery
end GroupApproximation
