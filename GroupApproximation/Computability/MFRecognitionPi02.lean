import GroupApproximation.Computability.CodedMicrostateEncoding
import GroupApproximation.Computability.EffectiveMicrostateSemantics
import GroupApproximation.Computability.EffectiveOperatorNormCode
import GroupApproximation.Computability.MicrostateNaturalize
import GroupApproximation.Computability.MicrostateNormalForm
import GroupApproximation.Computability.RationalMatrixEncoding

/-!
# A `Π⁰₂` upper bound for Operator-MF recognition

Open microstate inequalities permit exact Gaussian-rational unitary
approximants.  Power/Frobenius certificates then replace both strict operator
norm comparisons by total Boolean tests.  Together with the executable word
problem search this gives a computable checker whose `∀∃` truth condition is
exactly Operator-MF for the repository's concrete finite-presentation codes.

This file proves the upper bound only.  It makes no hardness or completeness
claim.
-/

namespace GroupApproximation
namespace MFRecognitionPi02

open Nat.Partrec
open ArithmeticalHierarchy
open PresentationCodes AdianRabinWordProblem RawWord
open EffectiveMatrixCode EffectiveMatrixCodePrimrec
open EffectiveOperatorNormCode
open CodedMicrostateEncoding
open EffectiveMicrostateSemantics
open MFMicrostate
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

/-! ## Strict-open microstate normal form -/

/-- The open finite packet used by rational approximation. -/
def PassesOpen (c : PresentationCode) (W : List (List (ℕ × Bool))) (k : ℕ)
    (M : Microstate c) : Prop :=
  (∀ r ∈ c.2, M.len r < 1 / ((k : ℝ) + 1)) ∧
    (∀ w ∈ W, 1 / 3 < M.len w)

/-- An open challenge is void or has an open-packet microstate. -/
def AnswersOpen (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (k : ℕ) : Prop :=
  (∃ w ∈ W, WordProblem c w) ∨ ∃ M : Microstate c, PassesOpen c W k M

private theorem finer_scale_lt (k : ℕ) :
    1 / ((((2 * k + 1 : ℕ) : ℝ)) + 1) < 1 / ((k : ℝ) + 1) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hrewrite : ((((2 * k + 1 : ℕ) : ℝ)) + 1) =
      2 * ((k : ℝ) + 1) := by push_cast; ring
  rw [hrewrite]
  calc
    1 / (2 * ((k : ℝ) + 1)) = (1 / 2 : ℝ) * (1 / ((k : ℝ) + 1)) := by
      field_simp
    _ < 1 * (1 / ((k : ℝ) + 1)) :=
      mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ = 1 / ((k : ℝ) + 1) := one_mul _

/-- Operator-MF is exactly the assertion that every strict-open challenge is
answered.  The forward direction creates slack by querying the closed normal
form at scale `2*k+1`; the backward direction uses the same area argument with
fixed separation `1/3`. -/
theorem isOperatorMF_iff_forall_openAnswers (c : PresentationCode) :
    IsOperatorMF (Carrier c) ↔ ∀ W k, AnswersOpen c W k := by
  classical
  constructor
  · intro hMF W k
    rcases (MFMicrostate.isOperatorMF_iff_forall_answers c).1 hMF W (2 * k + 1) with
      hvoid | ⟨M, hrel, hsep⟩
    · exact Or.inl hvoid
    · refine Or.inr ⟨M, ?_, ?_⟩
      · intro r hr
        exact (hrel r hr).trans_lt (finer_scale_lt k)
      · intro w hw
        have := hsep w hw
        linarith
  · intro h
    refine (show IsWeakMF (Carrier c) from ⟨1 / 3, by norm_num, ?_⟩).isOperatorMF
    intro F ε hε
    set wd : Carrier c → List (ℕ × Bool) := Function.surjInv (ev_surjective c)
      with hwd
    have hwdspec : ∀ g : Carrier c, ev c (wd g) = g := fun g ↦
      Function.surjInv_eq (ev_surjective c) g
    set pairs : Finset (Carrier c × Carrier c) :=
      (F ×ˢ F).filter fun q ↦ q.1 ≠ q.2 with hpairs
    set W : List (List (ℕ × Bool)) :=
      pairs.toList.map fun q ↦ invWord (wd q.1) ++ wd q.2 with hW
    set mulWords : List (List (ℕ × Bool)) :=
      (F ×ˢ F).toList.map fun q ↦
        invWord (wd q.1 ++ wd q.2) ++ wd (q.1 * q.2) with hmul
    have hmultriv : ∀ u ∈ mulWords, WordProblem c u := by
      intro u hu
      rw [hmul, List.mem_map] at hu
      obtain ⟨q, _hq, rfl⟩ := hu
      rw [← ev_eq_one_iff, ev_append, ev_invWord, ev_append, hwdspec,
        hwdspec, hwdspec, inv_mul_cancel]
    obtain ⟨N, hN⟩ := exists_area_bound_list c mulWords hmultriv
    obtain ⟨k, hk⟩ := exists_nat_gt ((N : ℝ) / ε)
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hNk : (N : ℝ) * (1 / ((k : ℝ) + 1)) ≤ ε := by
      have h1 : (N : ℝ) / ε < (k : ℝ) + 1 := by linarith
      have h2 : (N : ℝ) < ε * ((k : ℝ) + 1) := by
        have := (div_lt_iff₀ hε).1 h1
        linarith
      rw [mul_one_div]
      exact (div_le_iff₀ hkpos).2 (by linarith)
    rcases h W k with hvoid | ⟨M, hrel, hsep⟩
    · exfalso
      obtain ⟨w, hw, hwtriv⟩ := hvoid
      rw [hW, List.mem_map] at hw
      obtain ⟨q, hq, rfl⟩ := hw
      rw [Finset.mem_toList, hpairs, Finset.mem_filter] at hq
      rw [← ev_eq_one_iff, ev_append, ev_invWord, hwdspec, hwdspec,
        inv_mul_eq_one] at hwtriv
      exact hq.2 hwtriv
    refine ⟨{
      carrier := M.model
      nonempty := M.card_pos
      map := fun g ↦ ((M.hom (wordOf c (wd g)) :
        Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ)
      isUnitary := fun g ↦ (M.hom (wordOf c (wd g))).2
      multiplicative := ?_
      separated := ?_ }⟩
    · intro g hg h' hh'
      have hmemword :
          (invWord (wd g ++ wd h') ++ wd (g * h')) ∈ mulWords := by
        rw [hmul, List.mem_map]
        refine ⟨(g, h'), ?_, rfl⟩
        rw [Finset.mem_toList, Finset.mem_product]
        exact ⟨hg, hh'⟩
      have hval : M.len (invWord (wd g ++ wd h') ++ wd (g * h')) =
          opLength M.model
            ((M.hom (wordOf c (wd g)) * M.hom (wordOf c (wd h')))⁻¹ *
              M.hom (wordOf c (wd (g * h')))) := by
        rw [Microstate.len_def, wordOf_append, wordOf_invWord, wordOf_append,
          map_mul, map_inv, map_mul]
      have hbound := hN M (1 / ((k : ℝ) + 1)) (by positivity)
        (fun r hr ↦ (hrel r hr).le) _ hmemword
      rw [hval] at hbound
      have hfinal := hbound.trans hNk
      rw [opLength_inv_mul] at hfinal
      simpa using hfinal
    · intro g hg h' hh' hne
      have hmemword : (invWord (wd h') ++ wd g) ∈ W := by
        rw [hW, List.mem_map]
        refine ⟨(h', g), ?_, rfl⟩
        rw [Finset.mem_toList, hpairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hh', hg⟩, Ne.symm hne⟩
      have hval : M.len (invWord (wd h') ++ wd g) =
          opLength M.model
            ((M.hom (wordOf c (wd h')))⁻¹ * M.hom (wordOf c (wd g))) := by
        rw [Microstate.len_def, wordOf_append, wordOf_invWord, map_mul, map_inv]
      have hbound := (hsep _ hmemword).le
      rw [hval, opLength_inv_mul] at hbound
      simpa using hbound

/-! ## Finite-word perturbation and rationalization -/

private theorem norm_inv_sub_inv_unitary {Y : FiniteModel}
    (u v : Matrix.unitaryGroup Y ℂ) :
    ‖((u⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) -
        ((v⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)‖ =
      ‖(u : Matrix Y Y ℂ) - (v : Matrix Y Y ℂ)‖ := by
  have hu : (((u⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)) =
      (u : Matrix Y Y ℂ)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  have hv : (((v⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)) =
      (v : Matrix Y Y ℂ)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  rw [hu, hv]
  have hsub : (u : Matrix Y Y ℂ)ᴴ - (v : Matrix Y Y ℂ)ᴴ =
      ((u : Matrix Y Y ℂ) - (v : Matrix Y Y ℂ))ᴴ := by simp
  rw [hsub, ← Matrix.star_eq_conjTranspose, norm_star]

private theorem norm_mul_sub_mul_unitary_le {Y : FiniteModel}
    (a b c d : Matrix.unitaryGroup Y ℂ) :
    ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
        (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ ≤
      ‖(a : Matrix Y Y ℂ) - (b : Matrix Y Y ℂ)‖ +
        ‖(c : Matrix Y Y ℂ) - (d : Matrix Y Y ℂ)‖ := by
  have h1 : ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
      (b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ)‖ =
      ‖(a : Matrix Y Y ℂ) - (b : Matrix Y Y ℂ)‖ := by
    rw [← Matrix.sub_mul, CStarRing.norm_mul_mem_unitary _ c.2]
  have h2 : ‖(b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
      (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ =
      ‖(c : Matrix Y Y ℂ) - (d : Matrix Y Y ℂ)‖ := by
    rw [← Matrix.mul_sub, CStarRing.norm_mem_unitary_mul _ b.2]
  calc
    ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
        (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ ≤
        ‖(a : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
            (b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ)‖ +
          ‖(b : Matrix Y Y ℂ) * (c : Matrix Y Y ℂ) -
            (b : Matrix Y Y ℂ) * (d : Matrix Y Y ℂ)‖ :=
      norm_sub_le_add_norm_sub _ _ _
    _ = _ := by rw [h1, h2]

/-- Evaluate one signed raw letter in a tuple of unitaries. -/
def tupleLetter {c : PresentationCode} {Y : FiniteModel}
    (U : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) (p : ℕ × Bool) :
    Matrix.unitaryGroup Y ℂ :=
  if p.2 then U (letterOf c p.1) else (U (letterOf c p.1))⁻¹

/-- Evaluate a raw word in a tuple of unitaries. -/
def tupleWord {c : PresentationCode} {Y : FiniteModel}
    (U : Fin (genCount c) → Matrix.unitaryGroup Y ℂ)
    (w : List (ℕ × Bool)) : Matrix.unitaryGroup Y ℂ :=
  (w.map (tupleLetter U)).prod

theorem microstate_hom_wordOf_eq_tupleWord {c : PresentationCode}
    (M : Microstate c) (w : List (ℕ × Bool)) :
    M.hom (wordOf c w) = tupleWord M.gen w := by
  induction w with
  | nil => simp [tupleWord]
  | cons p w ih =>
      obtain ⟨i, s⟩ := p
      cases s
      · rw [wordOf_cons_neg, map_mul, map_inv, ih]
        simp [tupleWord, tupleLetter, letterOf]
      · rw [wordOf_cons_pos, map_mul, ih]
        simp [tupleWord, tupleLetter, letterOf]

private theorem tupleLetter_gap {c : PresentationCode} {Y : FiniteModel}
    (U V : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) {η : ℝ}
    (hclose : ∀ i, ‖(U i : Matrix Y Y ℂ) - (V i : Matrix Y Y ℂ)‖ < η)
    (p : ℕ × Bool) :
    ‖(tupleLetter U p : Matrix Y Y ℂ) -
        (tupleLetter V p : Matrix Y Y ℂ)‖ < η := by
  obtain ⟨i, s⟩ := p
  cases s
  · simpa [tupleLetter] using
      (show ‖(((U (letterOf c i))⁻¹ : Matrix.unitaryGroup Y ℂ) :
          Matrix Y Y ℂ) -
          (((V (letterOf c i))⁻¹ : Matrix.unitaryGroup Y ℂ) :
            Matrix Y Y ℂ)‖ < η from by
        rw [norm_inv_sub_inv_unitary]
        exact hclose (letterOf c i))
  · simpa [tupleLetter] using hclose (letterOf c i)

/-- Telescoping bound for a finite word evaluated in two unitary tuples. -/
theorem tupleWord_gap_le {c : PresentationCode} {Y : FiniteModel}
    (U V : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) {η : ℝ}
    (hclose : ∀ i, ‖(U i : Matrix Y Y ℂ) - (V i : Matrix Y Y ℂ)‖ < η) :
    ∀ w : List (ℕ × Bool),
      ‖(tupleWord U w : Matrix Y Y ℂ) -
          (tupleWord V w : Matrix Y Y ℂ)‖ ≤ (w.length : ℝ) * η
  | [] => by simp [tupleWord]
  | p :: w => by
      have hstep := norm_mul_sub_mul_unitary_le
        (tupleLetter U p) (tupleLetter V p) (tupleWord U w) (tupleWord V w)
      have hp := (tupleLetter_gap U V hclose p).le
      have hw := tupleWord_gap_le U V hclose w
      simp only [tupleWord, List.map_cons, List.prod_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      calc
        ‖(tupleLetter U p : Matrix Y Y ℂ) *
            (tupleWord U w : Matrix Y Y ℂ) -
            (tupleLetter V p : Matrix Y Y ℂ) *
              (tupleWord V w : Matrix Y Y ℂ)‖ ≤
            ‖(tupleLetter U p : Matrix Y Y ℂ) -
              (tupleLetter V p : Matrix Y Y ℂ)‖ +
            ‖(tupleWord U w : Matrix Y Y ℂ) -
              (tupleWord V w : Matrix Y Y ℂ)‖ := hstep
        _ ≤ η + (w.length : ℝ) * η := add_le_add hp hw
        _ = ((w.length + 1 : ℕ) : ℝ) * η := by push_cast; ring

/-- Perturbing each generator by `η` changes the word displacement from the
identity by at most `length * η`. -/
theorem abs_tupleLength_sub_le {c : PresentationCode} {Y : FiniteModel}
    (U V : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) {η : ℝ}
    (hclose : ∀ i,
      ‖(U i : Matrix Y Y ℂ) - (V i : Matrix Y Y ℂ)‖ < η)
    (w : List (ℕ × Bool)) :
    |‖(tupleWord U w : Matrix Y Y ℂ) - 1‖ -
        ‖(tupleWord V w : Matrix Y Y ℂ) - 1‖| ≤
      (w.length : ℝ) * η := by
  refine (abs_norm_sub_norm_le
    ((tupleWord U w : Matrix Y Y ℂ) - 1)
    ((tupleWord V w : Matrix Y Y ℂ) - 1)).trans ?_
  have hgap := tupleWord_gap_le U V hclose w
  simpa only [sub_sub_sub_cancel_right] using hgap

/-- A finite list of positive word margins admits one positive generator
tolerance satisfying all length-weighted bounds. -/
theorem exists_word_tolerance (L : List (List (ℕ × Bool)))
    (margin : List (ℕ × Bool) → ℝ)
    (hmargin : ∀ w ∈ L, 0 < margin w) :
    ∃ η : ℝ, 0 < η ∧
      ∀ w ∈ L, (w.length : ℝ) * η < margin w := by
  induction L with
  | nil => exact ⟨1, by norm_num, by simp⟩
  | cons a L ih =>
      obtain ⟨η, hη, hL⟩ := ih (fun w hw ↦ hmargin w (List.mem_cons_of_mem _ hw))
      let δ : ℝ := min (margin a / ((a.length : ℝ) + 1)) η / 2
      have hma : 0 < margin a := hmargin a List.mem_cons_self
      have hδ : 0 < δ := by
        dsimp [δ]
        positivity
      refine ⟨δ, hδ, ?_⟩
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · have hle : δ < margin a / ((a.length : ℝ) + 1) := by
          dsimp [δ]
          have hmin : 0 < min (margin a / ((a.length : ℝ) + 1)) η := by
            positivity
          have hhalf : min (margin a / ((a.length : ℝ) + 1)) η / 2 <
              min (margin a / ((a.length : ℝ) + 1)) η := by linarith
          exact hhalf.trans_le (min_le_left _ _)
        have hlen : (a.length : ℝ) < (a.length : ℝ) + 1 := by linarith
        calc
          (a.length : ℝ) * δ ≤ ((a.length : ℝ) + 1) * δ :=
            mul_le_mul_of_nonneg_right hlen.le hδ.le
          _ < ((a.length : ℝ) + 1) *
              (margin a / ((a.length : ℝ) + 1)) :=
            mul_lt_mul_of_pos_left hle (by positivity)
          _ = margin a := by field_simp
      · have hδη : δ ≤ η := by
          dsimp [δ]
          have hmin := min_le_right (margin a / ((a.length : ℝ) + 1)) η
          nlinarith
        exact (mul_le_mul_of_nonneg_left hδη (by positivity)).trans_lt (hL w hw)

/-- Every strict-open microstate packet has a witness consisting of exactly
unitary Gaussian-rational matrix codes. -/
theorem exists_coded_openPasses {c : PresentationCode}
    {W : List (List (ℕ × Bool))} {k : ℕ} (M : Microstate c)
    (hM : PassesOpen c W k M) :
    ∃ d gens (hunitary : GeneratorsUnitary c d gens),
      PassesOpen c W k (toMicrostate c d gens hunitary) := by
  classical
  have hcard : Fintype.card M.model ≠ 0 := Nat.ne_of_gt M.card_pos
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hcard
  have hdim : Fintype.card M.model = dim d := by simpa [dim] using hd
  let e : M.model ≃ Fin (dim d) :=
    (Fintype.equivFin M.model).trans (finCongr hdim)
  let N : Microstate c := M.reindex (naturalFiniteModel (dim d)) e
  have hNlen (w : List (ℕ × Bool)) : N.len w = M.len w := by
    exact Microstate.reindex_len M (naturalFiniteModel (dim d)) e w
  have hNrel : ∀ r ∈ c.2, N.len r < 1 / ((k : ℝ) + 1) := by
    intro r hr
    rw [hNlen]
    exact hM.1 r hr
  have hNsep : ∀ w ∈ W, 1 / 3 < N.len w := by
    intro w hw
    rw [hNlen]
    exact hM.2 w hw
  obtain ⟨ηr, hηr, hrelMargin⟩ := exists_word_tolerance c.2
    (fun r ↦ 1 / ((k : ℝ) + 1) - N.len r) (by
      intro r hr
      have := hNrel r hr
      linarith)
  obtain ⟨ηw, hηw, hwordMargin⟩ := exists_word_tolerance W
    (fun w ↦ N.len w - 1 / 3) (by
      intro w hw
      have := hNsep w hw
      linarith)
  let η : ℝ := min ηr ηw / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηr_le : η ≤ ηr := by
    dsimp [η]
    have := min_le_left ηr ηw
    nlinarith
  have hηw_le : η ≤ ηw := by
    dsimp [η]
    have := min_le_right ηr ηw
    nlinarith
  have hcodes : ∀ i : Fin (genCount c), ∃ C : MatrixCode,
      isUnitary d C ∧
        ‖(N.gen i : Matrix (Fin (dim d)) (Fin (dim d)) ℂ) -
          toMatrix d C‖ < η := by
    intro i
    exact RationalMatrixEncoding.exists_unitary_matrixCode_close d
      (N.gen i).2 hη
  choose code hcodeUnit hcodeClose using hcodes
  let gens : List MatrixCode := List.ofFn code
  have hgenerator (i : Fin (genCount c)) : generator d gens i = code i := by
    simp [generator, gens, List.getD_eq_getElem?_getD, i.isLt]
  have hunitary : GeneratorsUnitary c d gens := by
    intro i
    rw [hgenerator]
    exact hcodeUnit i
  let C : Microstate c := toMicrostate c d gens hunitary
  have hclose : ∀ i,
      ‖(N.gen i : Matrix (Fin (dim d)) (Fin (dim d)) ℂ) -
        (C.gen i : Matrix (Fin (dim d)) (Fin (dim d)) ℂ)‖ < η := by
    intro i
    simpa [C, toMicrostate, hgenerator i] using hcodeClose i
  have hgap (w : List (ℕ × Bool)) :
      |N.len w - C.len w| ≤ (w.length : ℝ) * η := by
    rw [Microstate.len_def, Microstate.len_def,
      microstate_hom_wordOf_eq_tupleWord,
      microstate_hom_wordOf_eq_tupleWord]
    exact abs_tupleLength_sub_le N.gen C.gen hclose w
  refine ⟨d, gens, hunitary, ?_, ?_⟩
  · intro r hr
    have hmarginη : (r.length : ℝ) * η <
        1 / ((k : ℝ) + 1) - N.len r :=
      (mul_le_mul_of_nonneg_left hηr_le (by positivity)).trans_lt
        (hrelMargin r hr)
    have habs := hgap r
    have hside : C.len r - N.len r ≤ (r.length : ℝ) * η :=
      (le_abs_self _).trans habs
    linarith
  · intro w hw
    have hmarginη : (w.length : ℝ) * η < N.len w - 1 / 3 :=
      (mul_le_mul_of_nonneg_left hηw_le (by positivity)).trans_lt
        (hwordMargin w hw)
    have habs := hgap w
    have hside : N.len w - C.len w ≤ (w.length : ℝ) * η :=
      (le_abs_self _).trans habs
    linarith

/-! ## The finite Boolean matrix checker -/

/-- The executable matrix whose norm is the displacement of a raw word. -/
def wordDefect (c : PresentationCode) (d : ℕ) (gens : List MatrixCode)
    (w : List (ℕ × Bool)) : MatrixCode :=
  matrixSub d (wordMatrix d c.1 gens w) (identity d)

/-- A direct Boolean test for semantic equality of two coded matrices on the
represented square. -/
def matrixEqCheck (d : ℕ) (A B : MatrixCode) : Bool :=
  decide (matrixEq d A B)

@[simp] theorem matrixEqCheck_eq_true_iff (d : ℕ) (A B : MatrixCode) :
    matrixEqCheck d A B = true ↔ matrixEq d A B := by
  simp [matrixEqCheck]

/-- Exact coded unitarity, expressed through the Boolean matrix equality
test rather than an analytic oracle. -/
def isUnitaryCheck (d : ℕ) (A : MatrixCode) : Bool :=
  matrixEqCheck d (matrixMul d (conjTranspose d A) A) (identity d)

@[simp] theorem isUnitaryCheck_eq_true_iff (d : ℕ) (A : MatrixCode) :
    isUnitaryCheck d A = true ↔ isUnitary d A := by
  simp [isUnitaryCheck, isUnitary]

/-- Check the bounded tuple of generators named by a presentation.  Missing
list entries are the coded identity, exactly as in `generator`. -/
def generatorTupleCheck (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) : Bool :=
  decide (GeneratorsUnitary c d gens)

@[simp] theorem generatorTupleCheck_eq_true_iff (c : PresentationCode)
    (d : ℕ) (gens : List MatrixCode) :
    generatorTupleCheck c d gens = true ↔ GeneratorsUnitary c d gens := by
  simp [generatorTupleCheck]

/-- One strict upper certificate for each relator, with exact packet length. -/
def UpperPacket (c : PresentationCode) (d k : ℕ)
    (gens : List MatrixCode) (certs : List ℕ) : Prop :=
  certs.length = c.2.length ∧
    ∀ i < c.2.length,
      upperNormCert d k (wordDefect c d gens (c.2.getD i []))
        (certs.getD i 0)

instance upperPacketDecidable (c : PresentationCode) (d k : ℕ)
    (gens : List MatrixCode) (certs : List ℕ) :
    Decidable (UpperPacket c d k gens certs) := by
  unfold UpperPacket
  infer_instance

/-- One strict lower-third certificate for each tested word, with exact packet
length. -/
def LowerPacket (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (d : ℕ) (gens : List MatrixCode) (certs : List ℕ) : Prop :=
  certs.length = W.length ∧
    ∀ i < W.length,
      lowerThirdCert d (wordDefect c d gens (W.getD i []))
        (certs.getD i 0)

instance lowerPacketDecidable (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (d : ℕ) (gens : List MatrixCode)
    (certs : List ℕ) : Decidable (LowerPacket c W d gens certs) := by
  unfold LowerPacket
  infer_instance

/-- Semantic validity of the finite matrix-answer encoding. -/
def MatrixAnswerValid (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer) : Prop :=
  GeneratorsUnitary c (matrixDimension a) (matrixGenerators a) ∧
    UpperPacket c (matrixDimension a) k (matrixGenerators a)
      (matrixUpperCertificates a) ∧
    LowerPacket c W (matrixDimension a) (matrixGenerators a)
      (matrixLowerCertificates a)

instance matrixAnswerValidDecidable (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer) :
    Decidable (MatrixAnswerValid c W k a) := by
  unfold MatrixAnswerValid
  infer_instance

/-- The complete Boolean matrix branch: exact unitarity, an upper certificate
for every relator, and a lower certificate for every tested word. -/
def matrixAnswerCheck (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer) : Bool :=
  decide (MatrixAnswerValid c W k a)

@[simp] theorem matrixAnswerCheck_eq_true_iff (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer) :
    matrixAnswerCheck c W k a = true ↔ MatrixAnswerValid c W k a := by
  simp [matrixAnswerCheck]

/-- Soundness of one accepted finite matrix answer. -/
theorem openPasses_of_matrixAnswerCheck_eq_true (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) (a : MatrixAnswer)
    (ha : matrixAnswerCheck c W k a = true) :
    ∃ hunitary : GeneratorsUnitary c (matrixDimension a) (matrixGenerators a),
      PassesOpen c W k
        (toMicrostate c (matrixDimension a) (matrixGenerators a) hunitary) := by
  have hvalid := (matrixAnswerCheck_eq_true_iff c W k a).1 ha
  refine ⟨hvalid.1, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, rfl⟩ := List.get_of_mem hr
    have hcert := hvalid.2.1.2 i.1 i.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2,
      Option.getD_some] at hcert
    rw [toMicrostate_len_eq_matrixSub]
    exact opNorm_lt_invSucc_of_upperNormCert _ _ _ _ hcert
  · intro w hw
    obtain ⟨i, rfl⟩ := List.get_of_mem hw
    have hcert := hvalid.2.2.2 i.1 i.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2,
      Option.getD_some] at hcert
    rw [toMicrostate_len_eq_matrixSub]
    exact one_third_lt_opNorm_of_lowerThirdCert _ _ _ hcert

/-- Completeness of the Boolean matrix branch for an already coded open
microstate packet. -/
theorem exists_matrixAnswerCheck_of_coded_openPasses
    (c : PresentationCode) (W : List (List (ℕ × Bool))) (k d : ℕ)
    (gens : List MatrixCode) (hunitary : GeneratorsUnitary c d gens)
    (hpass : PassesOpen c W k (toMicrostate c d gens hunitary)) :
    ∃ a : MatrixAnswer, matrixAnswerCheck c W k a = true := by
  classical
  have hupp : ∀ i : Fin c.2.length, ∃ m,
      upperNormCert d k (wordDefect c d gens (c.2.get i)) m := by
    intro i
    apply exists_upperNormCert_of_opNorm_lt_invSucc
    rw [← toMicrostate_len_eq_matrixSub]
    exact hpass.1 (c.2.get i) (List.get_mem c.2 i)
  choose upper hupper using hupp
  have hlow : ∀ i : Fin W.length, ∃ m,
      lowerThirdCert d (wordDefect c d gens (W.get i)) m := by
    intro i
    apply exists_lowerThirdCert_of_one_third_lt_opNorm
    rw [← toMicrostate_len_eq_matrixSub]
    exact hpass.2 (W.get i) (List.get_mem W i)
  choose lower hlower using hlow
  let upperList : List ℕ := List.ofFn upper
  let lowerList : List ℕ := List.ofFn lower
  let a : MatrixAnswer := (d, (gens, (upperList, lowerList)))
  refine ⟨a, (matrixAnswerCheck_eq_true_iff c W k a).2 ?_⟩
  refine ⟨hunitary, ?_, ?_⟩
  · constructor
    · simp [a, upperList]
    · intro i hi
      have hs : upperList.getD i 0 = upper ⟨i, hi⟩ := by
        simp [upperList, List.getD_eq_getElem?_getD, hi]
      rw [hs]
      simpa [a, wordDefect, List.getD_eq_getElem?_getD, hi] using
        hupper ⟨i, hi⟩
  · constructor
    · simp [a, lowerList]
    · intro i hi
      have hs : lowerList.getD i 0 = lower ⟨i, hi⟩ := by
        simp [lowerList, List.getD_eq_getElem?_getD, hi]
      rw [hs]
      simpa [a, wordDefect, List.getD_eq_getElem?_getD, hi] using
        hlower ⟨i, hi⟩

/-- Existential exactness of the finite matrix branch. -/
theorem exists_matrixAnswerCheck_iff (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) :
    (∃ a : MatrixAnswer, matrixAnswerCheck c W k a = true) ↔
      ∃ M : Microstate c, PassesOpen c W k M := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨hunitary, hpass⟩ :=
      openPasses_of_matrixAnswerCheck_eq_true c W k a ha
    exact ⟨toMicrostate c (matrixDimension a) (matrixGenerators a) hunitary,
      hpass⟩
  · rintro ⟨M, hM⟩
    obtain ⟨d, gens, hunitary, hpass⟩ := exists_coded_openPasses M hM
    exact exists_matrixAnswerCheck_of_coded_openPasses
      c W k d gens hunitary hpass

/-! ## Primitive recursiveness of the bounded exact checks -/

theorem primrec_wordDefect :
    Primrec fun z : (((PresentationCode × ℕ) × List MatrixCode) ×
      List (ℕ × Bool)) =>
      wordDefect z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hword : Primrec fun z : (((PresentationCode × ℕ) × List MatrixCode) ×
      List (ℕ × Bool)) =>
      wordMatrix z.1.1.2 z.1.1.1.1 z.1.2 z.2 :=
    primrec_wordMatrix.comp (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.fst.comp (Primrec.fst.comp
            (Primrec.fst.comp Primrec.fst))))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
  exact primrec_matrixSub.comp (Primrec.pair
    (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      hword)
    (primrec_identity.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_matrixEq :
    PrimrecPred fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixEq z.1.1 z.1.2 z.2 := by
  have hcoord : PrimrecRel fun (ij : ℕ × ℕ)
      (z : (ℕ × MatrixCode) × MatrixCode) =>
      RationalComplexCode.ComplexEq
        (entry z.1.1 z.1.2 ij.1 ij.2)
        (entry z.1.1 z.2 ij.1 ij.2) := by
    have hleft : Primrec fun p : (ℕ × ℕ) ×
        ((ℕ × MatrixCode) × MatrixCode) =>
        entry p.2.1.1 p.2.1.2 p.1.1 p.1.2 :=
      primrec_entry.comp (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
    have hright : Primrec fun p : (ℕ × ℕ) ×
        ((ℕ × MatrixCode) × MatrixCode) =>
        entry p.2.1.1 p.2.2 p.1.1 p.1.2 :=
      primrec_entry.comp (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
    exact RationalComplexCode.primrecRel_complexEq.comp hleft hright
  have hcol : PrimrecRel fun (j : ℕ)
      (z : ℕ × ((ℕ × MatrixCode) × MatrixCode)) =>
      RationalComplexCode.ComplexEq
        (entry z.2.1.1 z.2.1.2 z.1 j)
        (entry z.2.1.1 z.2.2 z.1 j) :=
    PrimrecRel.comp hcoord
      (Primrec.pair (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hcols : PrimrecRel fun (L : List ℕ)
      (z : ℕ × ((ℕ × MatrixCode) × MatrixCode)) =>
      ∀ j ∈ L,
        RationalComplexCode.ComplexEq
          (entry z.2.1.1 z.2.1.2 z.1 j)
          (entry z.2.1.1 z.2.2 z.1 j) :=
    PrimrecRel.forall_mem_list hcol
  have hrow : PrimrecRel fun (i : ℕ)
      (z : (ℕ × MatrixCode) × MatrixCode) =>
      ∀ j ∈ List.range (dim z.1.1),
        RationalComplexCode.ComplexEq
          (entry z.1.1 z.1.2 i j) (entry z.1.1 z.2 i j) :=
    PrimrecRel.comp hcols
      (Primrec.list_range.comp (primrec_dim.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.pair Primrec.fst Primrec.snd)
  have hrows : PrimrecRel fun (L : List ℕ)
      (z : (ℕ × MatrixCode) × MatrixCode) =>
      ∀ i ∈ L, ∀ j ∈ List.range (dim z.1.1),
        RationalComplexCode.ComplexEq
          (entry z.1.1 z.1.2 i j) (entry z.1.1 z.2 i j) :=
    PrimrecRel.forall_mem_list hrow
  refine (PrimrecRel.comp hrows
    (Primrec.list_range.comp
      (primrec_dim.comp (Primrec.fst.comp Primrec.fst))) Primrec.id).of_eq ?_
  intro z
  constructor
  · intro h i hi j hj
    exact h i (List.mem_range.2 hi) j (List.mem_range.2 hj)
  · intro h i hi j hj
    exact h i (List.mem_range.1 hi) j (List.mem_range.1 hj)

theorem primrec_matrixEqCheck :
    Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixEqCheck z.1.1 z.1.2 z.2 :=
  primrecPred_matrixEq.decide

theorem primrecPred_isUnitary :
    PrimrecPred fun z : ℕ × MatrixCode => isUnitary z.1 z.2 := by
  exact primrecPred_matrixEq.comp (Primrec.pair
    (Primrec.pair Primrec.fst
      (primrec_matrixMul.comp (Primrec.pair
        (Primrec.pair Primrec.fst
          (primrec_conjTranspose.comp Primrec.id)) Primrec.snd)))
    (primrec_identity.comp Primrec.fst))

theorem primrec_isUnitaryCheck :
    Primrec fun z : ℕ × MatrixCode => isUnitaryCheck z.1 z.2 := by
  exact primrecPred_isUnitary.decide.of_eq fun z => by
    simp [isUnitaryCheck, matrixEqCheck, isUnitary]

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_generatorsUnitary :
    PrimrecPred fun z : (PresentationCode × ℕ) × List MatrixCode =>
      GeneratorsUnitary z.1.1 z.1.2 z.2 := by
  have hitem : PrimrecRel fun (i : ℕ)
      (z : (PresentationCode × ℕ) × List MatrixCode) =>
      isUnitary z.1.2 (generator z.1.2 z.2 i) := by
    exact primrecPred_isUnitary.comp (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (primrec_generator.comp (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)) Primrec.fst)))
  have hall : PrimrecRel fun (L : List ℕ)
      (z : (PresentationCode × ℕ) × List MatrixCode) =>
      ∀ i ∈ L, isUnitary z.1.2 (generator z.1.2 z.2 i) :=
    PrimrecRel.forall_mem_list hitem
  refine (PrimrecRel.comp hall
    (Primrec.list_range.comp
      (primrec_genCount.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    Primrec.id).of_eq ?_
  intro z
  constructor
  · intro h i
    exact h i (List.mem_range.2 i.isLt)
  · intro h i hi
    exact h ⟨i, List.mem_range.1 hi⟩

theorem primrec_generatorTupleCheck :
    Primrec fun z : (PresentationCode × ℕ) × List MatrixCode =>
      generatorTupleCheck z.1.1 z.1.2 z.2 :=
  primrecPred_generatorsUnitary.decide

private abbrev UpperInput :=
  (((PresentationCode × ℕ) × ℕ) × List MatrixCode) × List ℕ

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_upperPacket :
    PrimrecPred fun z : UpperInput =>
      UpperPacket z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
  have hitem : PrimrecRel fun (i : ℕ) (z : UpperInput) =>
      upperNormCert z.1.1.1.2 z.1.1.2
        (wordDefect z.1.1.1.1 z.1.1.1.2 z.1.2
          (z.1.1.1.1.2.getD i []))
        (z.2.getD i 0) := by
    have hc : Primrec fun p : ℕ × UpperInput => p.2.1.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd)))
    have hd : Primrec fun p : ℕ × UpperInput => p.2.1.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd)))
    have hk : Primrec fun p : ℕ × UpperInput => p.2.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    have hgens : Primrec fun p : ℕ × UpperInput => p.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hrels : Primrec fun p : ℕ × UpperInput => p.2.1.1.1.1.2 :=
      Primrec.snd.comp hc
    have hrelator : Primrec fun p : ℕ × UpperInput =>
        p.2.1.1.1.1.2.getD p.1 [] :=
      (Primrec.list_getD ([] : List (ℕ × Bool))).comp hrels Primrec.fst
    have hdefect : Primrec fun p : ℕ × UpperInput =>
        wordDefect p.2.1.1.1.1 p.2.1.1.1.2 p.2.1.2
          (p.2.1.1.1.1.2.getD p.1 []) :=
      primrec_wordDefect.comp (Primrec.pair
        (Primrec.pair (Primrec.pair hc hd) hgens) hrelator)
    have hcert : Primrec fun p : ℕ × UpperInput => p.2.2.getD p.1 0 :=
      (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd) Primrec.fst
    exact primrecPred_upperNormCert.comp (Primrec.pair
      (Primrec.pair (Primrec.pair hd hk) hdefect) hcert)
  have hall : PrimrecRel fun (L : List ℕ) (z : UpperInput) =>
      ∀ i ∈ L,
        upperNormCert z.1.1.1.2 z.1.1.2
          (wordDefect z.1.1.1.1 z.1.1.1.2 z.1.2
            (z.1.1.1.1.2.getD i []))
          (z.2.getD i 0) :=
    PrimrecRel.forall_mem_list hitem
  have hforall : PrimrecPred fun z : UpperInput =>
      ∀ i ∈ List.range z.1.1.1.1.2.length,
        upperNormCert z.1.1.1.2 z.1.1.2
          (wordDefect z.1.1.1.1 z.1.1.1.2 z.1.2
            (z.1.1.1.1.2.getD i []))
          (z.2.getD i 0) :=
    PrimrecRel.comp hall
      (Primrec.list_range.comp (Primrec.list_length.comp
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))))
      Primrec.id
  have hlen : PrimrecPred fun z : UpperInput =>
      z.2.length = z.1.1.1.1.2.length :=
    Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))
  refine (PrimrecPred.and hlen hforall).of_eq ?_
  intro z
  simp only [UpperPacket]
  constructor
  · rintro ⟨hlen', h⟩
    exact ⟨hlen', fun i hi => h i (List.mem_range.2 hi)⟩
  · rintro ⟨hlen', h⟩
    exact ⟨hlen', fun i hi => h i (List.mem_range.1 hi)⟩

private abbrev LowerInput :=
  (((PresentationCode × List (List (ℕ × Bool))) × ℕ) × List MatrixCode) ×
    List ℕ

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_lowerPacket :
    PrimrecPred fun z : LowerInput =>
      LowerPacket z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
  have hitem : PrimrecRel fun (i : ℕ) (z : LowerInput) =>
      lowerThirdCert z.1.1.2
        (wordDefect z.1.1.1.1 z.1.1.2 z.1.2
          (z.1.1.1.2.getD i []))
        (z.2.getD i 0) := by
    have hc : Primrec fun p : ℕ × LowerInput => p.2.1.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd)))
    have hW : Primrec fun p : ℕ × LowerInput => p.2.1.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd)))
    have hd : Primrec fun p : ℕ × LowerInput => p.2.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    have hgens : Primrec fun p : ℕ × LowerInput => p.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hword : Primrec fun p : ℕ × LowerInput =>
        p.2.1.1.1.2.getD p.1 [] :=
      (Primrec.list_getD ([] : List (ℕ × Bool))).comp hW Primrec.fst
    have hdefect : Primrec fun p : ℕ × LowerInput =>
        wordDefect p.2.1.1.1.1 p.2.1.1.2 p.2.1.2
          (p.2.1.1.1.2.getD p.1 []) :=
      primrec_wordDefect.comp (Primrec.pair
        (Primrec.pair (Primrec.pair hc hd) hgens) hword)
    have hcert : Primrec fun p : ℕ × LowerInput => p.2.2.getD p.1 0 :=
      (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd) Primrec.fst
    exact primrecPred_lowerThirdCert.comp
      (Primrec.pair (Primrec.pair hd hdefect) hcert)
  have hall : PrimrecRel fun (L : List ℕ) (z : LowerInput) =>
      ∀ i ∈ L,
        lowerThirdCert z.1.1.2
          (wordDefect z.1.1.1.1 z.1.1.2 z.1.2
            (z.1.1.1.2.getD i []))
          (z.2.getD i 0) :=
    PrimrecRel.forall_mem_list hitem
  have hforall : PrimrecPred fun z : LowerInput =>
      ∀ i ∈ List.range z.1.1.1.2.length,
        lowerThirdCert z.1.1.2
          (wordDefect z.1.1.1.1 z.1.1.2 z.1.2
            (z.1.1.1.2.getD i []))
          (z.2.getD i 0) :=
    PrimrecRel.comp hall
      (Primrec.list_range.comp (Primrec.list_length.comp
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))))) Primrec.id
  have hlen : PrimrecPred fun z : LowerInput =>
      z.2.length = z.1.1.1.2.length :=
    Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
  refine (PrimrecPred.and hlen hforall).of_eq ?_
  intro z
  simp only [LowerPacket]
  constructor
  · rintro ⟨hlen', h⟩
    exact ⟨hlen', fun i hi => h i (List.mem_range.2 hi)⟩
  · rintro ⟨hlen', h⟩
    exact ⟨hlen', fun i hi => h i (List.mem_range.1 hi)⟩

private abbrev MatrixCheckInput :=
  ((PresentationCode × List (List (ℕ × Bool))) × ℕ) × MatrixAnswer

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_matrixAnswerValid :
    PrimrecPred fun z : MatrixCheckInput =>
      MatrixAnswerValid z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hc : Primrec fun z : MatrixCheckInput => z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hW : Primrec fun z : MatrixCheckInput => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec fun z : MatrixCheckInput => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hd : Primrec fun z : MatrixCheckInput => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hgens : Primrec fun z : MatrixCheckInput => z.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hupp : Primrec fun z : MatrixCheckInput => z.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hlow : Primrec fun z : MatrixCheckInput => z.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hunit : PrimrecPred fun z : MatrixCheckInput =>
      GeneratorsUnitary z.1.1.1 z.2.1 z.2.2.1 :=
    primrecPred_generatorsUnitary.comp
      (Primrec.pair (Primrec.pair hc hd) hgens)
  have hupper : PrimrecPred fun z : MatrixCheckInput =>
      UpperPacket z.1.1.1 z.2.1 z.1.2 z.2.2.1 z.2.2.2.1 :=
    primrecPred_upperPacket.comp (Primrec.pair
      (Primrec.pair (Primrec.pair (Primrec.pair hc hd) hk) hgens) hupp)
  have hlower : PrimrecPred fun z : MatrixCheckInput =>
      LowerPacket z.1.1.1 z.1.1.2 z.2.1 z.2.2.1 z.2.2.2.2 :=
    primrecPred_lowerPacket.comp (Primrec.pair
      (Primrec.pair (Primrec.pair (Primrec.pair hc hW) hd) hgens) hlow)
  exact PrimrecPred.and hunit (PrimrecPred.and hupper hlower)

theorem primrec_matrixAnswerCheck :
    Primrec fun z : MatrixCheckInput =>
      matrixAnswerCheck z.1.1.1 z.1.1.2 z.1.2 z.2 :=
  primrecPred_matrixAnswerValid.decide

/-! ## The full checker and the hierarchy upper bound -/

/-- Combine the executable void and matrix branches for one challenge. -/
def answerCheck (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (k : ℕ) : MFAnswerCertificate → Bool
  | Sum.inl a => voidAnswerCheck c W a
  | Sum.inr a => matrixAnswerCheck c W k a

theorem primrec_answerCheck :
    Primrec fun z : ((PresentationCode × List (List (ℕ × Bool))) × ℕ) ×
      MFAnswerCertificate => answerCheck z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hvoid : Primrec₂ fun
      (z : ((PresentationCode × List (List (ℕ × Bool))) × ℕ) ×
        MFAnswerCertificate) (a : VoidAnswer) =>
      voidAnswerCheck z.1.1.1 z.1.1.2 a := by
    exact (primrec_voidAnswerCheck.comp (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      Primrec.snd)).to₂
  have hmatrix : Primrec₂ fun
      (z : ((PresentationCode × List (List (ℕ × Bool))) × ℕ) ×
        MFAnswerCertificate) (a : MatrixAnswer) =>
      matrixAnswerCheck z.1.1.1 z.1.1.2 z.1.2 a := by
    exact (primrec_matrixAnswerCheck.comp (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)).to₂
  exact (Primrec.sumCasesOn Primrec.snd hvoid hmatrix).of_eq fun z => by
    cases z.2 <;> rfl

/-- Both a challenge and its proposed finite answer are total natural-number
decoders.  Thus `MFChecker` is an ordinary Boolean matrix on naturals. -/
def MFChecker (c : PresentationCode) (n cert : ℕ) : Bool :=
  answerCheck c (challengeAt n).1 (challengeAt n).2
    (answerCertificateAt cert)

theorem primrec_MFChecker :
    Primrec fun z : (PresentationCode × ℕ) × ℕ =>
      MFChecker z.1.1 z.1.2 z.2 := by
  exact primrec_answerCheck.comp (Primrec.pair
    (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp
          (primrec_challengeAt.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.snd.comp
        (primrec_challengeAt.comp (Primrec.snd.comp Primrec.fst))))
    (primrec_answerCertificateAt.comp Primrec.snd))

theorem computable₂_MFChecker :
    Computable₂ fun z : PresentationCode × ℕ => MFChecker z.1 z.2 :=
  primrec_MFChecker.to_comp.to₂

theorem exists_answerCheck_iff (c : PresentationCode)
    (W : List (List (ℕ × Bool))) (k : ℕ) :
    (∃ cert : MFAnswerCertificate, answerCheck c W k cert = true) ↔
      AnswersOpen c W k := by
  constructor
  · rintro ⟨cert, hcert⟩
    cases cert with
    | inl a =>
        exact Or.inl ((exists_voidAnswerCheck_iff c W).1 ⟨a, hcert⟩)
    | inr a =>
        exact Or.inr ((exists_matrixAnswerCheck_iff c W k).1 ⟨a, hcert⟩)
  · rintro (hvoid | hmatrix)
    · obtain ⟨a, ha⟩ := (exists_voidAnswerCheck_iff c W).2 hvoid
      exact ⟨Sum.inl a, ha⟩
    · obtain ⟨a, ha⟩ := (exists_matrixAnswerCheck_iff c W k).2 hmatrix
      exact ⟨Sum.inr a, ha⟩

/-- Decoding the natural answer coordinate loses no witnesses. -/
theorem exists_MFChecker_iff (c : PresentationCode) (n : ℕ) :
    (∃ cert : ℕ, MFChecker c n cert = true) ↔
      AnswersOpen c (challengeAt n).1 (challengeAt n).2 := by
  constructor
  · rintro ⟨cert, hcert⟩
    exact (exists_answerCheck_iff c (challengeAt n).1 (challengeAt n).2).1
      ⟨answerCertificateAt cert, hcert⟩
  · intro h
    obtain ⟨cert, hcert⟩ :=
      (exists_answerCheck_iff c (challengeAt n).1 (challengeAt n).2).2 h
    exact ⟨Encodable.encode cert, by simpa [MFChecker] using hcert⟩

/-- The requested exact `∀∃` checker normal form. -/
theorem isOperatorMF_iff_forall_exists_MFChecker (c : PresentationCode) :
    IsOperatorMF (Carrier c) ↔
      ∀ n, ∃ cert : ℕ, MFChecker c n cert = true := by
  rw [isOperatorMF_iff_forall_openAnswers]
  rw [← forall_challengeAt_iff]
  apply forall_congr'
  intro n
  exact (exists_MFChecker_iff c n).symm

/-- For one presentation and one challenge, existence of a finite accepted
answer is recursively enumerable. -/
theorem rePred_MFAnswer :
    REPred fun z : PresentationCode × ℕ =>
      ∃ cert : ℕ, MFChecker z.1 z.2 cert = true :=
  WordProblemRE.rePred_exists_eq_true computable₂_MFChecker

/-- Operator-MF recognition for concrete finite-presentation codes lies in
`Π⁰₂`.  This is an upper bound only. -/
theorem operatorMFCode_pi02 :
    Pi02 fun c : PresentationCode => IsOperatorMF (Carrier c) := by
  refine pi02_of_re_family rePred_MFAnswer ?_
  intro c
  exact isOperatorMF_iff_forall_exists_MFChecker c

/-- Non-operator-MF recognition for concrete finite-presentation codes lies in
the second existential level, unconditionally and with the finite checker
above as its witness system. -/
theorem nonOperatorMFCode_sigma02 :
    Sigma02 fun c : PresentationCode => ¬ IsOperatorMF (Carrier c) := by
  exact (sigma02_compl_iff
    (fun c : PresentationCode => IsOperatorMF (Carrier c))).2
    operatorMFCode_pi02

end
end MFRecognitionPi02
end GroupApproximation
