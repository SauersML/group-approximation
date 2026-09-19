import GroupApproximation.Computability.EnumeratedPresentationCodes
import GroupApproximation.Computability.FixedLiteralMarkedQuery

/-!
# The fixed literal marked query on standard enumerated presentations

This is the exact eight-generator, forty-one-relator marked-homomorphism query
on `EnumeratedPresentationCodes.PresentationCode`.  Its checker uses the
uniform raw normal-closure certificates derived in
`EnumeratedPresentationCodes`; no recursive-presentation hypothesis is an
input.  The final theorem identifies the executable query with arbitrary
homomorphisms from the fixed literal non-MF marked group.
-/

namespace GroupApproximation
namespace EnumeratedFixedMarkedQuery

open FixedMarkedQueryHierarchy LiteralNonMFPresentation
open EnumeratedPresentationCodes

noncomputable section

abbrev RawWord := Higman.RawWord
abbrev Assignment := FixedLiteralMarkedQuery.Assignment
abbrev RelatorCertificates := List.Vector WordCertificate 41
abbrev WitnessData := Assignment × RelatorCertificates

/-- Evaluation of a raw target word in the group denoted by a standard code. -/
def targetEval (c : PresentationCode) (w : RawWord) : Carrier c :=
  Higman.evalRaw (fun n => (PresentedGroup.of n : Carrier c)) w

theorem targetEval_eq_one_iff (c : PresentationCode) (w : RawWord) :
    targetEval c w = 1 ↔ ∃ cert : WordCertificate, wordCheck (c, w) cert = true :=
  wordCheck_complete c w

theorem targetEval_surjective (c : PresentationCode) :
    Function.Surjective (targetEval c) := by
  intro x
  obtain ⟨g, rfl⟩ := PresentedGroup.mk_surjective (relatorSet c) x
  refine ⟨g.toWord, ?_⟩
  rw [targetEval, Higman.evalRaw_presentedGroup_of]
  congr 1
  rw [Higman.freeEval_eq]
  simpa using FreeGroup.mk_toWord (x := g)

/-- The target word and certificate check for one literal source relator. -/
def relatorCheck (x : PresentationCode × WitnessData) (i : Fin 41) : Bool :=
  wordCheck (x.1,
    FixedLiteralMarkedQuery.substitute x.2.1
      (FixedLiteralMarkedQuery.sourceRelatorRaw i)) (x.2.2.get i)

theorem primrec_relatorCheck : Primrec₂ relatorCheck := by
  have hc : Primrec fun z : (PresentationCode × WitnessData) × Fin 41 => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec fun z : (PresentationCode × WitnessData) × Fin 41 => z.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hw : Primrec fun z : (PresentationCode × WitnessData) × Fin 41 =>
      FixedLiteralMarkedQuery.substitute z.1.2.1
        (FixedLiteralMarkedQuery.sourceRelatorRaw z.2) :=
    FixedLiteralMarkedQuery.primrec_substitute.comp ha
      (FixedLiteralMarkedQuery.primrec_sourceRelatorRaw.comp Primrec.snd)
  have hp : Primrec fun z : (PresentationCode × WitnessData) × Fin 41 =>
      z.1.2.2.get z.2 :=
    Primrec.vector_get.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  exact primrec_wordCheck.comp (Primrec.pair hc hw) hp

def relatorsValid (x : PresentationCode × WitnessData) : Prop :=
  ∀ i : Fin 41, relatorCheck x i = true

noncomputable instance relatorsValid_decidable
    (x : PresentationCode × WitnessData) : Decidable (relatorsValid x) :=
  Classical.dec _

def relatorsValidCheck (x : PresentationCode × WitnessData) : Bool :=
  decide (relatorsValid x)

theorem relatorsValidCheck_eq_true_iff (x : PresentationCode × WitnessData) :
    relatorsValidCheck x = true ↔ relatorsValid x := decide_eq_true_iff

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

def witnessFailure
    (z : ((PresentationCode × ℕ) × ℕ) × WitnessData) : Bool :=
  bif relatorsValidCheck (z.1.1.1, z.2) then
    (Encodable.decode (α := WordCertificate) z.1.2).map
      (fun cert => wordCheck
        (z.1.1.1, FixedLiteralMarkedQuery.substitute z.2.1
          FixedLiteralMarkedQuery.sourceMarkRaw) cert) |>.getD false
  else true

def failureCheck (x : PresentationCode × ℕ) (derivation : ℕ) : Bool :=
  (Encodable.decode (α := WitnessData) x.2).map
    (fun witness => witnessFailure ((x, derivation), witness)) |>.getD true

theorem computable_failureCheck : Computable₂ failureCheck := by
  have h : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      failureCheck z.1 z.2 := by
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
          Encodable.decode (α := WordCertificate) z.1.2 :=
        Primrec.decode.comp (Primrec.snd.comp Primrec.fst)
      have hword : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          FixedLiteralMarkedQuery.substitute z.2.1
            FixedLiteralMarkedQuery.sourceMarkRaw :=
        FixedLiteralMarkedQuery.primrec_substitute.comp ha
          (Primrec.const FixedLiteralMarkedQuery.sourceMarkRaw)
      have hcheck : Primrec₂ fun
          (z : ((PresentationCode × ℕ) × ℕ) × WitnessData)
          (cert : WordCertificate) =>
            wordCheck (z.1.1.1,
              FixedLiteralMarkedQuery.substitute z.2.1
                FixedLiteralMarkedQuery.sourceMarkRaw) cert :=
        primrec_wordCheck.comp
          (Primrec.pair (hc.comp Primrec.fst) (hword.comp Primrec.fst)) Primrec.snd
      have hmapped : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          (Encodable.decode (α := WordCertificate) z.1.2).map
            (fun cert => wordCheck
              (z.1.1.1, FixedLiteralMarkedQuery.substitute z.2.1
                FixedLiteralMarkedQuery.sourceMarkRaw) cert) :=
        Primrec.option_map hderiv hcheck
      have hchallenge : Primrec fun z : ((PresentationCode × ℕ) × ℕ) × WitnessData =>
          ((Encodable.decode (α := WordCertificate) z.1.2).map
            (fun cert => wordCheck
              (z.1.1.1, FixedLiteralMarkedQuery.substitute z.2.1
                FixedLiteralMarkedQuery.sourceMarkRaw) cert)).getD false :=
        Primrec.option_getD.comp hmapped (Primrec.const false)
      exact Primrec.cond hvalid hchallenge (Primrec.const true)
    have hmapped : Primrec fun z : (PresentationCode × ℕ) × ℕ =>
        (Encodable.decode (α := WitnessData) z.1.2).map
          (fun witness => witnessFailure (z, witness)) :=
      Primrec.option_map hwit hsome
    exact Primrec.option_getD.comp hmapped (Primrec.const true)
  exact h.to_comp.to₂

/-- The fixed literal marked query on standard enumerated presentations. -/
def literalQuery : EffectiveQuery PresentationCode where
  failureCheck := failureCheck
  failureCheck_computable := computable_failureCheck

theorem targetEval_substitute (c : PresentationCode) (a : Assignment) (w : RawWord) :
    targetEval c (FixedLiteralMarkedQuery.substitute a w) =
      Higman.evalRaw (fun n => targetEval c (a.get (FixedLiteralMarkedQuery.fin8 n))) w := by
  induction w with
  | nil => simp [FixedLiteralMarkedQuery.substitute, targetEval]
  | cons p w ih =>
      obtain ⟨n, b⟩ := p
      cases b with
      | false =>
          change targetEval c
              (RawWord.invWord (a.get (FixedLiteralMarkedQuery.fin8 n)) ++
                FixedLiteralMarkedQuery.substitute a w) = _
          rw [targetEval, Higman.evalRaw_append]
          change _ = (targetEval c (a.get (FixedLiteralMarkedQuery.fin8 n)))⁻¹ * _
          rw [← targetEval]
          have hinv : targetEval c
              (RawWord.invWord (a.get (FixedLiteralMarkedQuery.fin8 n))) =
                (targetEval c (a.get (FixedLiteralMarkedQuery.fin8 n)))⁻¹ := by
            rw [RawWord.invWord, ← Higman.invRaw_eq, targetEval,
              Higman.evalRaw_invRaw]
            rfl
          rw [hinv]
          change _ * targetEval c (FixedLiteralMarkedQuery.substitute a w) = _
          rw [ih]
      | true =>
          change targetEval c
              (a.get (FixedLiteralMarkedQuery.fin8 n) ++
                FixedLiteralMarkedQuery.substitute a w) = _
          rw [targetEval, Higman.evalRaw_append]
          change targetEval c (a.get (FixedLiteralMarkedQuery.fin8 n)) *
              targetEval c (FixedLiteralMarkedQuery.substitute a w) = _
          rw [ih]
          simp

theorem targetEval_substitute_sourceRaw (c : PresentationCode) (a : Assignment)
    (w : FreeGroup Generator) :
    targetEval c (FixedLiteralMarkedQuery.substitute a
      (FixedLiteralMarkedQuery.sourceRaw w)) =
      FreeGroup.lift
        (fun g => targetEval c (a.get (generatorEquivFin8 g))) w := by
  rw [targetEval_substitute]
  simpa using FixedLiteralMarkedQuery.evalRaw_sourceRaw
    (f := fun g => targetEval c (a.get (generatorEquivFin8 g))) w

def ConcreteSurvives (c : PresentationCode) : Prop :=
  ∃ a : Assignment,
    (∀ i : Fin 41, targetEval c
      (FixedLiteralMarkedQuery.substitute a
        (FixedLiteralMarkedQuery.sourceRelatorRaw i)) = 1) ∧
      targetEval c (FixedLiteralMarkedQuery.substitute a
        FixedLiteralMarkedQuery.sourceMarkRaw) ≠ 1

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
        have hvalidCheck : relatorsValidCheck (c, (a, certificates)) = true := by
          cases hv : relatorsValidCheck (c, (a, certificates)) with
          | false =>
              have h := hall 0
              simp [literalQuery, failureCheck, hwitness, witnessFailure, hv] at h
          | true => rfl
        have hvalid : relatorsValid (c, (a, certificates)) :=
          (relatorsValidCheck_eq_true_iff _).1 hvalidCheck
        refine ⟨a, ?_, ?_⟩
        · intro i
          exact (targetEval_eq_one_iff c _).2
            ⟨certificates.get i, hvalid i⟩
        · intro hmark
          obtain ⟨cert, hcert⟩ := (targetEval_eq_one_iff c _).1 hmark
          have h := hall (Encodable.encode cert)
          simp [literalQuery, failureCheck, hwitness, witnessFailure,
            hvalidCheck, Encodable.encodek, hcert] at h
  · rintro ⟨a, hrel, hmark⟩
    have hexists : ∀ i : Fin 41, ∃ cert : WordCertificate,
        wordCheck (c, FixedLiteralMarkedQuery.substitute a
          (FixedLiteralMarkedQuery.sourceRelatorRaw i)) cert = true := by
      intro i
      exact (targetEval_eq_one_iff c _).1 (hrel i)
    let certificates : RelatorCertificates :=
      List.Vector.ofFn fun i => Classical.choose (hexists i)
    have hcertificates : relatorsValid (c, (a, certificates)) := by
      intro i
      simpa [relatorCheck, certificates] using Classical.choose_spec (hexists i)
    have hvalidCheck : relatorsValidCheck (c, (a, certificates)) = true :=
      (relatorsValidCheck_eq_true_iff _).2 hcertificates
    refine ⟨Encodable.encode (a, certificates), ?_⟩
    intro derivation
    cases hderivation : Encodable.decode (α := WordCertificate) derivation with
    | none =>
        simp [literalQuery, failureCheck, witnessFailure,
          Encodable.encodek, hvalidCheck, hderivation]
    | some cert =>
        have hcheck : wordCheck (c,
            FixedLiteralMarkedQuery.substitute a
              FixedLiteralMarkedQuery.sourceMarkRaw) cert = false := by
          cases hs : wordCheck (c,
              FixedLiteralMarkedQuery.substitute a
                FixedLiteralMarkedQuery.sourceMarkRaw) cert with
          | false => rfl
          | true =>
              exfalso
              apply hmark
              exact (targetEval_eq_one_iff c _).2 ⟨cert, hs⟩
        simp [literalQuery, failureCheck, witnessFailure,
          Encodable.encodek, hvalidCheck, hderivation, hcheck]

def HomSurvives (c : PresentationCode) : Prop :=
  ∃ φ : MarkedGroup →* Carrier c, φ mark ≠ 1

theorem hom_wordInMarkedGroup (c : PresentationCode)
    (φ : MarkedGroup →* Carrier c) (w : FreeGroup Generator) :
    φ (wordInMarkedGroup w) =
      FreeGroup.lift (fun g => φ (PresentedGroup.of g)) w := by
  refine freeGroup_hom_eq_on_generators
    (f := φ.comp wordInMarkedGroup)
    (g := FreeGroup.lift (fun g => φ (PresentedGroup.of g))) ?_ w
  intro g
  rw [MonoidHom.comp_apply,
    show wordInMarkedGroup (FreeGroup.of g) = PresentedGroup.of g from rfl,
    FreeGroup.lift_apply_of]

theorem concrete_iff_homSurvives (c : PresentationCode) :
    ConcreteSurvives c ↔ HomSurvives c := by
  constructor
  · rintro ⟨a, hrel, hmark⟩
    let f : Generator → Carrier c :=
      fun g => targetEval c (a.get (generatorEquivFin8 g))
    have hkills : ∀ r ∈ relators, FreeGroup.lift f r = 1 := by
      intro r hr
      obtain ⟨i, hi⟩ := FixedLiteralMarkedQuery.exists_sourceRelator_eq hr
      subst r
      simpa [f, FixedLiteralMarkedQuery.sourceRelatorRaw,
        targetEval_substitute_sourceRaw] using hrel i
    let φ : MarkedGroup →* Carrier c := PresentedGroup.toGroup hkills
    refine ⟨φ, ?_⟩
    intro htrivial
    apply hmark
    simpa [φ, f, FixedLiteralMarkedQuery.sourceMarkRaw,
      targetEval_substitute_sourceRaw, presentedToGroup_mk] using htrivial
  · rintro ⟨φ, hφ⟩
    let a : Assignment := List.Vector.ofFn fun i =>
      Classical.choose
        (targetEval_surjective c
          (φ (PresentedGroup.of (generatorEquivFin8.symm i))))
    have ha (i : Fin 8) :
        targetEval c (a.get i) =
          φ (PresentedGroup.of (generatorEquivFin8.symm i)) := by
      simpa [a] using Classical.choose_spec
        (targetEval_surjective c
          (φ (PresentedGroup.of (generatorEquivFin8.symm i))))
    have hgen (g : Generator) :
        targetEval c (a.get (generatorEquivFin8 g)) =
          φ (PresentedGroup.of g) := by simpa using ha (generatorEquivFin8 g)
    refine ⟨a, ?_, ?_⟩
    · intro i
      rw [FixedLiteralMarkedQuery.sourceRelatorRaw,
        targetEval_substitute_sourceRaw]
      simp only [hgen]
      rw [← hom_wordInMarkedGroup c φ]
      rw [PresentedGroup.one_of_mem
        (FixedLiteralMarkedQuery.sourceRelator_mem i), map_one]
    · intro hmark
      rw [FixedLiteralMarkedQuery.sourceMarkRaw,
        targetEval_substitute_sourceRaw] at hmark
      simp only [hgen] at hmark
      rw [← hom_wordInMarkedGroup c φ] at hmark
      exact hφ hmark

theorem survives_iff_homSurvives (c : PresentationCode) :
    Survives literalQuery c ↔ HomSurvives c :=
  (survives_iff_concrete c).trans (concrete_iff_homSurvives c)

theorem kills_iff_forall_hom_kills (c : PresentationCode) :
    Kills literalQuery c ↔ ∀ φ : MarkedGroup →* Carrier c, φ mark = 1 := by
  rw [kills_iff_not_survives, survives_iff_homSurvives]
  simp [HomSurvives]

theorem not_isOperatorMF_of_survives (c : PresentationCode)
    (h : Survives literalQuery c) : ¬ IsOperatorMF (Carrier c) := by
  letI : Countable (Carrier c) := (targetEval_surjective c).countable
  obtain ⟨φ, hφ⟩ := (survives_iff_homSurvives c).1 h
  exact SeededSelfAwareMFCompiler.quotient_not_isOperatorMF_of_invisible_mark_survives
    LiteralNonMFEndpoint.literal_mark_normMFInvisible φ hφ

theorem survives_sigma02 : ArithmeticalHierarchy.Sigma02 (Survives literalQuery) :=
  FixedMarkedQueryHierarchy.survives_sigma02 literalQuery

theorem kills_pi02 : ArithmeticalHierarchy.Pi02 (Kills literalQuery) :=
  FixedMarkedQueryHierarchy.kills_pi02 literalQuery

end

end EnumeratedFixedMarkedQuery
end GroupApproximation
