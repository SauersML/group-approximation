import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificateDerivation
import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificateSyntax
import GroupApproximation.Computability.MFRecognitionOpenCore

/-!
# The printed certificate of `prop:mf-upper-bound`: the decision, and the
forward direction

The second of three modules.  It carries

* `PrintedCertificateInputs`, the hypothesis structure through which Tarski's
  theorem and the effectivity of the printed encoding enter --- nothing is
  proved and nothing is postulated, so every consumer downstream shows the
  citations in its own statement;
* the relation `C(P,n,c)` (`PrintedC`) and its decidability
  (`decidable_printedC`);
* the local-model calculus of the printed forward direction: `U_j = V(x̄_j)`
  (`microstateOfLocalModel`), the adjoint estimate
  (`norm_localModel_inv_sub_conjTranspose_le`), and the induction
  `‖w(U) - V(w̄)‖ ≤ 2ℓε` (`gap_le`).

Printed sentences covered here: `9eae4d68673a`, `6aa84a1ea64e`,
`75dbc7ef237f`, `453aeb3d66bf`, `3190c7e7c5e7`, `98f3d22b2327`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Certificates

open Matrix PresentationCodes AdianRabinWordProblem RawWord MFMicrostate

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

universe u

/-! ## The inputs of the printed certificate route -/

-- LITERATURE INPUT (assumed): Tarski, quantifier elimination for real closed
-- fields, in the field `tarski`.  The remaining fields are the effectivity of
-- the printed encoding, which the manuscript asserts and does not prove.
/-- The hypotheses the printed certificate route takes as given.  Nothing here
is proved and nothing here is postulated: a consumer that wants the printed
conclusion of `prop:mf-upper-bound` takes a term of this structure as an
argument, so every theorem downstream carries the citations visibly in its own
statement.

* `tarski` --- Tarski's theorem, sentence `9eae4d68673a`.
* `encode`, `encode_spec` --- the printed polynomial encoding of `Φ(P,n,c)`
  described in sentences `a0d0247bea30` and `9f1f2f176f18`, whose atoms and
  their correctness *are* proved, in `PrintedTarskiCertificateSyntax`
  (`mem_unitaryGroup_iff_entry_equations`, `star_mul_re_im`,
  `l2_opNorm_le_iff_quadraticForm_nonneg`,
  `le_l2_opNorm_iff_exists_unit_vector`); what is assumed is only the
  bookkeeping that names a variable for each real coordinate, expands each word
  into its degree-two step equations, and conjoins the finitely many atoms.
* `phiDecision_computable` --- that deciding the encoded sentence is uniformly
  effective in the code, the scale and the certificate.
* `wellFormedCheck`, `wellFormedCheck_computable`, `wellFormedCheck_spec` ---
  that the combinatorial half of `C` is uniformly effective.  The predicate
  itself is already decidable outright (`instDecidableWellFormed`); only its
  uniform effectivity is assumed. -/
structure PrintedCertificateInputs where
  /-- Tarski's theorem for the first-order theory of the ordered field `ℝ`. -/
  tarski : TarskiInput
  /-- The first-order sentence encoding `Φ(P,n,c)`. -/
  encode : (PresentationCode × ℕ) × PrintedCertificate → RealFormula
  /-- Its truth at the zero assignment is exactly `Φ(P,n,c)`. -/
  encode_spec : ∀ (P : PresentationCode) (n : ℕ) (c : PrintedCertificate),
    ((encode ((P, n), c)).Holds fun _ => 0) ↔ PhiSpec P n c
  /-- Tarski's procedure, applied to the encoding, is computable. -/
  phiDecision_computable :
    Computable fun z => tarski.decideFormula (encode z)
  /-- The well-formedness check of a printed certificate. -/
  wellFormedCheck : (PresentationCode × ℕ) × PrintedCertificate → Bool
  /-- It is computable. -/
  wellFormedCheck_computable : Computable wellFormedCheck
  /-- It decides well-formedness. -/
  wellFormedCheck_spec : ∀ (P : PresentationCode) (n : ℕ)
      (c : PrintedCertificate),
    wellFormedCheck ((P, n), c) = true ↔ WellFormed P n c

/-- `prop:mf-upper-bound`, proof sentence `9eae4d68673a`, first clause: "Thus
`Φ(P,n,c)` is a sentence of the first-order theory of the ordered field of real
numbers."

The variables are the real and imaginary coordinates `U_j = A_j + i B_j` of the
`k` matrices, together with the auxiliary vectors of
`le_l2_opNorm_iff_exists_unit_vector`.  Unitarity is the polynomial system of
`mem_unitaryGroup_iff_entry_equations` and `star_mul_re_im`; each upper bound
`‖r_i(U) - 1‖ ≤ 2^{-n}` is the quadratic-form inequality of
`l2_opNorm_le_iff_quadraticForm_nonneg`, universally quantified over a vector;
each lower bound `‖w(U) - 1‖ ≥ 1/4` is the existential condition of
`le_l2_opNorm_iff_exists_unit_vector`.  Relators and `S`-words are finite in
number, so the whole condition is one `RealFormula.exList` over a
`RealFormula.andList`. -/
theorem phi_isFirstOrderSentence (I : PrintedCertificateInputs)
    (P : PresentationCode) (n : ℕ) (c : PrintedCertificate) :
    ∃ φ : RealFormula, (φ.Holds fun _ => 0) ↔ PhiSpec P n c :=
  ⟨I.encode ((P, n), c), I.encode_spec P n c⟩

/-- `prop:mf-upper-bound`, proof sentence `9eae4d68673a`, second clause: "and
its truth is decidable by Tarski's theorem~\cite{Tarski}."

The decision is uniform in `(P, n, c)`: apply Tarski's procedure to the
encoding.  Correctness is the composition of the two cited facts, and needs no
further hypothesis. -/
theorem exists_computable_phiDecision (I : PrintedCertificateInputs) :
    ∃ f : (PresentationCode × ℕ) × PrintedCertificate → Bool, Computable f ∧
      ∀ (P : PresentationCode) (n : ℕ) (c : PrintedCertificate),
        f ((P, n), c) = true ↔ PhiSpec P n c :=
  ⟨fun z => I.tarski.decideFormula (I.encode z), I.phiDecision_computable,
    fun P n c =>
      (I.tarski.decideFormula_iff (I.encode ((P, n), c))).trans
        (I.encode_spec P n c)⟩

/-! ## The relation `C` -/

/-- `prop:mf-upper-bound`, proof sentence `6aa84a1ea64e`: "Let `C(P,n,c)` hold
when `c` is a well-formed certificate at scale `n` whose `T`-expressions check
and `Φ(P,n,c)` holds." -/
def PrintedC (P : PresentationCode) (n : ℕ) (c : PrintedCertificate) : Prop :=
  WellFormed P n c ∧ PhiSpec P n c

/-- The combinatorial half of `C` is decidable outright
(`instDecidableWellFormed`); this is its uniform effectivity. -/
theorem computable_wellFormedCheck (I : PrintedCertificateInputs) :
    ∃ g : (PresentationCode × ℕ) × PrintedCertificate → Bool, Computable g ∧
      ∀ (P : PresentationCode) (n : ℕ) (c : PrintedCertificate),
        g ((P, n), c) = true ↔ WellFormed P n c :=
  ⟨I.wellFormedCheck, I.wellFormedCheck_computable, I.wellFormedCheck_spec⟩

/-- `prop:mf-upper-bound`, proof sentence `75dbc7ef237f`: "Then `C` is
decidable."

Both halves are decided: the combinatorial half by inspection of the finite
certificate, and the matrix half by Tarski's theorem. -/
theorem decidable_printedC (I : PrintedCertificateInputs) :
    ∃ f : (PresentationCode × ℕ) × PrintedCertificate → Bool, Computable f ∧
      ∀ (P : PresentationCode) (n : ℕ) (c : PrintedCertificate),
        f ((P, n), c) = true ↔ PrintedC P n c := by
  obtain ⟨g, hg, hgspec⟩ := computable_wellFormedCheck I
  obtain ⟨f, hf, hfspec⟩ := exists_computable_phiDecision I
  refine ⟨fun z => g z && f z, ?_, ?_⟩
  · refine (Computable.cond hg hf (Computable.const false)).of_eq ?_
    intro z
    cases g z <;> simp
  · intro P n c
    rw [Bool.and_eq_true, hgspec P n c, hfspec P n c]
    exact Iff.rfl

/-! ## The forward direction -/

/-- Reducing a letter into the alphabet does not change the element it
names. -/
theorem ev_letter_mod (P : PresentationCode) (j : ℕ) (b : Bool) :
    ev P [(((letterOf P j : Fin (genCount P)) : ℕ), b)] = ev P [(j, b)] := by
  have h : wordOf P [(((letterOf P j : Fin (genCount P)) : ℕ), b)]
      = wordOf P [(j, b)] := by
    simp only [wordOf_def, List.map_cons, List.map_nil, letterOf_val_letterOf]
  exact congrArg (evHom P) h

/-- A negative letter names the inverse of the corresponding generator. -/
theorem ev_letter_false (P : PresentationCode) (j : ℕ) :
    ev P [(j, false)] = (ev P [(j, true)])⁻¹ := by
  have h : invWord [(j, true)] = [(j, false)] := rfl
  rw [← h, ev_invWord]

/-- `prop:mf-upper-bound`, proof sentence `453aeb3d66bf`: "For `g ∈ F` we have
`g^{-1} ∈ F` and `‖V(g)V(g^{-1}) - 1‖ ≤ ε`, so `‖V(g^{-1}) - V(g)^*‖ ≤ ε`." -/
theorem norm_localModel_inv_sub_conjTranspose_le {G : Type u} [Group G]
    {F : Finset G} {ε : ℝ} (Lm : LocalModel G F ε) (h1 : (1 : G) ∈ F)
    {g : G} (hg : g ∈ F) (hginv : g⁻¹ ∈ F) :
    ‖Lm.V g⁻¹ - (Lm.V g)ᴴ‖ ≤ ε := by
  have hmul := Lm.multiplicative g hg g⁻¹ hginv
    (by rw [mul_inv_cancel]; exact h1)
  rw [mul_inv_cancel, Lm.V_one] at hmul
  have hAstar : (Lm.V g)ᴴ * Lm.V g = 1 := by
    have hu := Lm.isUnitary g
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    exact hu
  have hfac : (Lm.V g)ᴴ * (Lm.V g * Lm.V g⁻¹ - 1) = Lm.V g⁻¹ - (Lm.V g)ᴴ := by
    rw [mul_sub, mul_one, ← mul_assoc, hAstar, one_mul]
  rw [← hfac, CStarRing.norm_mem_unitary_mul _
    (conjTranspose_mem_unitaryGroup (Lm.isUnitary g)), norm_sub_rev]
  exact hmul

section LocalModelCalculus

variable {P : PresentationCode} {F : Finset (Carrier P)} {ε : ℝ}

/-- `prop:mf-upper-bound`, proof sentence `3190c7e7c5e7`: "Put `U_j = V(x̄_j)`,
where `w̄` denotes the image of a word `w` in `G_P`."  The tuple
`(U_1, …, U_k)` on the local model's finite dimension is a microstate. -/
def microstateOfLocalModel (Lm : LocalModel (Carrier P) F ε) : Microstate P where
  model := Lm.carrier
  card_pos := Lm.nonempty
  gen := fun j => ⟨Lm.V (ev P [((j : ℕ), true)]), Lm.isUnitary _⟩

/-- The values of the local model, read in the unitary group of its model. -/
def localUnitary (Lm : LocalModel (Carrier P) F ε) (g : Carrier P) :
    Matrix.unitaryGroup Lm.carrier ℂ :=
  ⟨Lm.V g, Lm.isUnitary g⟩

theorem localUnitary_coe (Lm : LocalModel (Carrier P) F ε) (g : Carrier P) :
    ((localUnitary Lm g : Matrix.unitaryGroup Lm.carrier ℂ) :
      Matrix Lm.carrier Lm.carrier ℂ) = Lm.V g := rfl

theorem gen_microstateOfLocalModel (Lm : LocalModel (Carrier P) F ε) (j : ℕ) :
    (microstateOfLocalModel Lm).gen (letterOf P j)
      = localUnitary Lm (ev P [(j, true)]) := by
  apply Subtype.ext
  show Lm.V (ev P [(((letterOf P j : Fin (genCount P)) : ℕ), true)])
      = Lm.V (ev P [(j, true)])
  rw [ev_letter_mod]

/-- The printed `w(U)`, for the microstate `U_j = V(x̄_j)`. -/
def evalAt (Lm : LocalModel (Carrier P) F ε) (u : List (ℕ × Bool)) :
    Matrix.unitaryGroup Lm.carrier ℂ :=
  (microstateOfLocalModel Lm).hom (wordOf P u)

theorem evalAt_nil (Lm : LocalModel (Carrier P) F ε) : evalAt Lm [] = 1 := by
  rw [evalAt, wordOf_nil, map_one]
  rfl

theorem evalAt_cons (Lm : LocalModel (Carrier P) F ε) (p : ℕ × Bool)
    (u : List (ℕ × Bool)) :
    evalAt Lm (p :: u) = evalAt Lm [p] * evalAt Lm u := by
  rw [evalAt, evalAt, evalAt, wordOf_cons, map_mul]
  rfl

theorem evalAt_letter_pos (Lm : LocalModel (Carrier P) F ε) (j : ℕ) :
    evalAt Lm [(j, true)] = localUnitary Lm (ev P [(j, true)]) := by
  have h : evalAt Lm [(j, true)]
      = (microstateOfLocalModel Lm).gen (letterOf P j) := by
    show FreeGroup.lift (microstateOfLocalModel Lm).gen
        (wordOf P [(j, true)]) = _
    rw [wordOf_pos]
    apply FreeGroup.lift_apply_of
  rw [h, gen_microstateOfLocalModel]

theorem evalAt_letter_neg (Lm : LocalModel (Carrier P) F ε) (j : ℕ) :
    evalAt Lm [(j, false)] = (localUnitary Lm (ev P [(j, true)]))⁻¹ := by
  have h : evalAt Lm [(j, false)]
      = ((microstateOfLocalModel Lm).gen (letterOf P j))⁻¹ := by
    show FreeGroup.lift (microstateOfLocalModel Lm).gen
        (wordOf P [(j, false)]) = _
    rw [wordOf_neg, map_inv]
    congr 1
    apply FreeGroup.lift_apply_of
  rw [h, gen_microstateOfLocalModel]
  rfl

/-- The microstate displacement of a word is the printed `‖w(U) - 1‖`. -/
theorem len_microstateOfLocalModel (Lm : LocalModel (Carrier P) F ε)
    (u : List (ℕ × Bool)) :
    (microstateOfLocalModel Lm).len u =
      ‖((evalAt Lm u : Matrix.unitaryGroup Lm.carrier ℂ) :
        Matrix Lm.carrier Lm.carrier ℂ) - 1‖ := by
  rw [Microstate.len_def, opLength]
  rfl

/-- The printed quantity `‖w(U) - V(w̄)‖`. -/
def gap (Lm : LocalModel (Carrier P) F ε) (u : List (ℕ × Bool)) : ℝ :=
  ‖((evalAt Lm u : Matrix.unitaryGroup Lm.carrier ℂ) :
      Matrix Lm.carrier Lm.carrier ℂ) -
    ((localUnitary Lm (ev P u) : Matrix.unitaryGroup Lm.carrier ℂ) :
      Matrix Lm.carrier Lm.carrier ℂ)‖

theorem gap_nil (Lm : LocalModel (Carrier P) F ε) : gap Lm [] = 0 := by
  have h : ((localUnitary Lm (ev P ([] : List (ℕ × Bool))) :
      Matrix.unitaryGroup Lm.carrier ℂ) :
        Matrix Lm.carrier Lm.carrier ℂ) = 1 := by
    rw [localUnitary_coe, ev_nil, Lm.V_one]
  simp only [gap, evalAt_nil, h]
  simp

/-- One letter is read to within `ε`: a positive letter exactly, a negative
letter by the adjoint estimate of sentence `453aeb3d66bf`. -/
theorem gap_letter_le (Lm : LocalModel (Carrier P) F ε) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier P) ∈ F) (hmem : ∀ q : ℕ × Bool, ev P [q] ∈ F)
    (p : ℕ × Bool) : gap Lm [p] ≤ ε := by
  obtain ⟨j, b⟩ := p
  cases b
  · have hcoe : (((localUnitary Lm (ev P [(j, true)]))⁻¹ :
        Matrix.unitaryGroup Lm.carrier ℂ) :
          Matrix Lm.carrier Lm.carrier ℂ) = (Lm.V (ev P [(j, true)]))ᴴ := by
      rw [← Matrix.star_eq_conjTranspose]
      rfl
    simp only [gap, evalAt_letter_neg, hcoe, localUnitary_coe]
    rw [ev_letter_false, norm_sub_rev]
    refine norm_localModel_inv_sub_conjTranspose_le Lm h1 (hmem (j, true)) ?_
    rw [← ev_letter_false]
    exact hmem (j, false)
  · simp only [gap, evalAt_letter_pos]
    simpa using hε

/-- `prop:mf-upper-bound`, proof sentence `98f3d22b2327`: "For a word
`w = y_1 ⋯ y_ℓ` of length `ℓ ≤ L`, all of whose prefixes have images in `F`,
induction on `ℓ` gives `‖w(U) - V(w̄)‖ ≤ 2ℓε`."

Read from the other end: peeling the first letter turns a word into one letter
and a shorter word whose image is again in `F`; the hypothesis is that every
tail `w.drop i` has its image in `F`. -/
theorem gap_le (Lm : LocalModel (Carrier P) F ε) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier P) ∈ F) (hmem : ∀ q : ℕ × Bool, ev P [q] ∈ F) :
    ∀ u : List (ℕ × Bool), (∀ i : ℕ, ev P (u.drop i) ∈ F) →
      gap Lm u ≤ 2 * u.length * ε
  | [], _ => by
      rw [gap_nil]
      simp
  | p :: u, htail => by
      have hmemu : ev P u ∈ F := by
        have hu := htail 1
        rwa [List.drop_succ_cons, List.drop_zero] at hu
      have hmempu : ev P (p :: u) ∈ F := by
        have hpu := htail 0
        rwa [List.drop_zero] at hpu
      have hih := gap_le Lm hε h1 hmem u (fun i => by
        have hi := htail (i + 1)
        rwa [List.drop_succ_cons] at hi)
      have hletter := gap_letter_le Lm hε h1 hmem p
      have hsplit : ev P (p :: u) = ev P [p] * ev P u := ev_append P [p] u
      have hcoemul :
          ((evalAt Lm (p :: u) : Matrix.unitaryGroup Lm.carrier ℂ) :
              Matrix Lm.carrier Lm.carrier ℂ)
            = ((evalAt Lm [p] : Matrix.unitaryGroup Lm.carrier ℂ) :
                Matrix Lm.carrier Lm.carrier ℂ) *
              ((evalAt Lm u : Matrix.unitaryGroup Lm.carrier ℂ) :
                Matrix Lm.carrier Lm.carrier ℂ) := by
        rw [evalAt_cons]
        rfl
      have hmulbound :
          ‖((localUnitary Lm (ev P [p]) : Matrix.unitaryGroup Lm.carrier ℂ) :
                Matrix Lm.carrier Lm.carrier ℂ) *
              ((localUnitary Lm (ev P u) : Matrix.unitaryGroup Lm.carrier ℂ) :
                Matrix Lm.carrier Lm.carrier ℂ) -
            ((localUnitary Lm (ev P (p :: u)) :
                Matrix.unitaryGroup Lm.carrier ℂ) :
              Matrix Lm.carrier Lm.carrier ℂ)‖ ≤ ε := by
        have hprod := Lm.multiplicative (ev P [p]) (hmem p) (ev P u) hmemu
          (by rw [← hsplit]; exact hmempu)
        rw [← hsplit] at hprod
        simp only [localUnitary_coe]
        rw [norm_sub_rev]
        exact hprod
      have hpair := MFRecognitionPi02.norm_mul_sub_mul_unitary_le
        (evalAt Lm [p]) (localUnitary Lm (ev P [p])) (evalAt Lm u)
        (localUnitary Lm (ev P u))
      have htri :
          ‖((evalAt Lm [p] : Matrix.unitaryGroup Lm.carrier ℂ) :
                Matrix Lm.carrier Lm.carrier ℂ) *
              ((evalAt Lm u : Matrix.unitaryGroup Lm.carrier ℂ) :
                Matrix Lm.carrier Lm.carrier ℂ) -
            ((localUnitary Lm (ev P (p :: u)) :
                Matrix.unitaryGroup Lm.carrier ℂ) :
              Matrix Lm.carrier Lm.carrier ℂ)‖
            ≤ ‖((evalAt Lm [p] : Matrix.unitaryGroup Lm.carrier ℂ) :
                  Matrix Lm.carrier Lm.carrier ℂ) *
                ((evalAt Lm u : Matrix.unitaryGroup Lm.carrier ℂ) :
                  Matrix Lm.carrier Lm.carrier ℂ) -
                ((localUnitary Lm (ev P [p]) :
                    Matrix.unitaryGroup Lm.carrier ℂ) :
                  Matrix Lm.carrier Lm.carrier ℂ) *
                  ((localUnitary Lm (ev P u) :
                      Matrix.unitaryGroup Lm.carrier ℂ) :
                    Matrix Lm.carrier Lm.carrier ℂ)‖ +
              ‖((localUnitary Lm (ev P [p]) :
                    Matrix.unitaryGroup Lm.carrier ℂ) :
                  Matrix Lm.carrier Lm.carrier ℂ) *
                ((localUnitary Lm (ev P u) :
                    Matrix.unitaryGroup Lm.carrier ℂ) :
                  Matrix Lm.carrier Lm.carrier ℂ) -
                ((localUnitary Lm (ev P (p :: u)) :
                    Matrix.unitaryGroup Lm.carrier ℂ) :
                  Matrix Lm.carrier Lm.carrier ℂ)‖ := by
        rw [← sub_add_sub_cancel
          (((evalAt Lm [p] : Matrix.unitaryGroup Lm.carrier ℂ) :
              Matrix Lm.carrier Lm.carrier ℂ) *
            ((evalAt Lm u : Matrix.unitaryGroup Lm.carrier ℂ) :
              Matrix Lm.carrier Lm.carrier ℂ))
          (((localUnitary Lm (ev P [p]) : Matrix.unitaryGroup Lm.carrier ℂ) :
              Matrix Lm.carrier Lm.carrier ℂ) *
            ((localUnitary Lm (ev P u) : Matrix.unitaryGroup Lm.carrier ℂ) :
              Matrix Lm.carrier Lm.carrier ℂ))
          ((localUnitary Lm (ev P (p :: u)) :
              Matrix.unitaryGroup Lm.carrier ℂ) :
            Matrix Lm.carrier Lm.carrier ℂ)]
        exact norm_add_le _ _
      have hgapcons : gap Lm (p :: u) ≤ gap Lm [p] + gap Lm u + ε := by
        simp only [gap] at hih hletter ⊢
        rw [hcoemul]
        linarith [htri, hpair, hmulbound]
      have hlen : ((p :: u).length : ℝ) = (u.length : ℝ) + 1 := by simp
      rw [hlen]
      linarith [hih, hletter, hgapcons]

end LocalModelCalculus

end

end Certificates
end MFRecognition
end Manuscript
end GroupApproximation
