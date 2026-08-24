import GroupApproximation.Sofic.ActiveCoreAlmostRepresentation
import GroupApproximation.Sofic.FiniteGroupCoronaExactification
import GroupApproximation.Sofic.OpToHSShadowResidual

/-!
# Finite-order normal generators and the MF radical

The main theorem in this file identifies MF invisibility with universal
Hilbert--Schmidt invisibility for a finite-order normal generator of a finitely
generated group.  Its analytic engine is quantitative active-core reblocking.
-/

namespace GroupApproximation
namespace FiniteOrderNormalGenerator

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G]
variable {X : ℕ → FiniteModel}

/-- Evaluation of an ambient packet word commutes with passage to the norm
matrix corona. -/
theorem quotient_mk_ambientWord
    {I : Type*} [Fintype I] [DecidableEq I] [∀ n, Nonempty (X n)]
    (W : ∀ n, I → Matrix.unitaryGroup (X n) ℂ)
    (l : List I) :
    (QuotientGroup.mk (fun n ↦ TorsionActiveCore.ambientWord (W n) l) :
        NormMatrixCoronaUnitary X) =
      (l.map fun g ↦
        (QuotientGroup.mk (fun n ↦ W n g) : NormMatrixCoronaUnitary X)).prod := by
  induction l with
  | nil =>
      change QuotientGroup.mk (1 : ∀ n, Matrix.unitaryGroup (X n) ℂ) = 1
      exact map_one (QuotientGroup.mk' (nullCofiniteOpSubgroup X))
  | cons i l ih =>
      change QuotientGroup.mk
          ((fun n ↦ W n i) *
            (fun n ↦ TorsionActiveCore.ambientWord (W n) l)) = _
      rw [QuotientGroup.mk_mul, ih]
      rfl

set_option maxHeartbeats 400000 in
/-- Coordinate packet lifts of a corona representation respect every group
word relation in operator norm. -/
theorem ambientWordsRespectGroup_of_corona
    [∀ n, Nonempty (X n)] (S : Finset G)
    (rho : G →* NormMatrixCoronaUnitary X)
    (W : ∀ n, S → Matrix.unitaryGroup (X n) ℂ)
    (hW : ∀ i : S, QuotientGroup.mk (fun n ↦ W n i) = rho i) :
    ActiveCoreAlmostRepresentation.AmbientWordsRespectGroup S W := by
  classical
  intro l₁ l₂ heval ε hε
  have hclass :
      (QuotientGroup.mk (fun n ↦ TorsionActiveCore.ambientWord (W n) l₁) :
          NormMatrixCoronaUnitary X) =
        QuotientGroup.mk (fun n ↦ TorsionActiveCore.ambientWord (W n) l₂) := by
    rw [quotient_mk_ambientWord W, quotient_mk_ambientWord W]
    simp_rw [hW]
    change (l₁.map (rho ∘ fun i : S ↦ (i : G))).prod =
      (l₂.map (rho ∘ fun i : S ↦ (i : G))).prod
    simpa only [map_list_prod, List.map_map] using congrArg rho heval
  have hnull :
      (fun n ↦ TorsionActiveCore.ambientWord (W n) l₁)⁻¹ *
          (fun n ↦ TorsionActiveCore.ambientWord (W n) l₂) ∈
        nullCofiniteOpSubgroup X := QuotientGroup.eq.mp hclass
  have hev := hnull ε hε
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn ↦ ?_⟩
  have := hN n hn
  change opLength (X n)
    ((TorsionActiveCore.ambientWord (W n) l₁)⁻¹ *
      TorsionActiveCore.ambientWord (W n) l₂) < ε at this
  rw [opLength_inv_mul] at this
  rw [norm_sub_rev]
  exact this.le

omit [Group G] in
/-- Conjugate-product evaluation commutes with passage to the norm matrix
corona. -/
theorem quotient_mk_conjugateWord
    [∀ n, Nonempty (X n)]
    (R : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (C : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (l : List (G × Bool)) :
    (QuotientGroup.mk (fun n ↦ TorsionActiveCore.conjugateWord (R n)
        (l.map fun p ↦ (C p.1 n, p.2))) : NormMatrixCoronaUnitary X) =
      ConjWord.conjWord
        (QuotientGroup.mk R : NormMatrixCoronaUnitary X)
        (l.map fun p ↦
          ((QuotientGroup.mk (C p.1) : NormMatrixCoronaUnitary X), p.2)) := by
  induction l with
  | nil =>
      change QuotientGroup.mk (1 : ∀ n, Matrix.unitaryGroup (X n) ℂ) = 1
      exact map_one (QuotientGroup.mk' (nullCofiniteOpSubgroup X))
  | cons p l ih =>
      obtain ⟨c, positive⟩ := p
      simp only [List.map_cons]
      rw [ConjWord.conjWord_cons]
      change QuotientGroup.mk
        ((fun n ↦ TorsionActiveCore.conjugateFactor (R n) (C c n) positive) *
          (fun n ↦ TorsionActiveCore.conjugateWord (R n)
            (l.map fun p ↦ (C p.1 n, p.2)))) = _
      rw [QuotientGroup.mk_mul, ih]
      unfold TorsionActiveCore.conjugateFactor
      cases positive <;> rfl

/-- A conjugate-word packet built from coordinate lifts represents the chosen
finite generating packet in the corona. -/
theorem quotient_mk_conjugateWordPacket
    [∀ n, Nonempty (X n)] (S : Finset G) (a : G)
    (words : S → List (G × Bool))
    (hwords : ∀ i : S, ConjWord.conjWord a (words i) = i)
    (rho : G →* NormMatrixCoronaUnitary X)
    (R : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hR : QuotientGroup.mk R = rho a)
    (C : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hC : ∀ g, QuotientGroup.mk (C g) = rho g) (i : S) :
    QuotientGroup.mk (fun n ↦
        TorsionActiveCore.conjugateWordPacket (R n)
          (fun j : S ↦ (words j).map fun p ↦ (C p.1 n, p.2)) i) = rho i := by
  change QuotientGroup.mk (fun n ↦ TorsionActiveCore.conjugateWord (R n)
      ((words i).map fun p ↦ (C p.1 n, p.2))) = rho i
  rw [quotient_mk_conjugateWord R C (words i), hR]
  simp_rw [hC]
  rw [← ConjWord.map_conjWord]
  rw [hwords]

/-- Finite generator data adapted to one normal generator.  The marked packet
entry uses the literal singleton conjugate word, which is what makes its
coordinate matrix exactly the torsion lift rather than merely corona-equal to
it. -/
structure NormalGeneratorPacket (G : Type) [Group G] (a : G) where
  S : Finset G
  symmetric : ∀ g ∈ S, g⁻¹ ∈ S
  generates : Subgroup.closure (S : Set G) = ⊤
  mark : S
  mark_value : (mark : G) = a
  words : S → List (G × Bool)
  word_value : ∀ i, ConjWord.conjWord a (words i) = i
  mark_word : words mark = [(1, true)]

/-- A finitely generated group normally generated by `a` admits a finite
packet of conjugate-product words with a literal marked entry. -/
theorem exists_normalGeneratorPacket [Group.FG G] (a : G)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) :
    Nonempty (NormalGeneratorPacket G a) := by
  classical
  obtain ⟨_, F, _, hF⟩ := Group.fg_iff'.mp (inferInstance : Group.FG G)
  let U : Finset G := insert a F
  let S : Finset G := U ∪ U.image fun g ↦ g⁻¹
  have haS : a ∈ S := by simp [S, U]
  let i₀ : S := ⟨a, haS⟩
  have hsymm : ∀ g ∈ S, g⁻¹ ∈ S := by
    intro g hg
    simp only [S, Finset.mem_union, Finset.mem_image] at hg ⊢
    rcases hg with hg | ⟨x, hx, rfl⟩
    · exact Or.inr ⟨g, hg, rfl⟩
    · exact Or.inl (by simpa using hx)
  have hFS : F ⊆ S := by
    intro g hg
    exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hg)
  have hclosure : Subgroup.closure (S : Set G) = ⊤ := by
    apply top_unique
    rw [← hF]
    exact Subgroup.closure_mono hFS
  have hex (i : S) : ∃ l : List (G × Bool), ConjWord.conjWord a l = i := by
    simpa using ConjWord.exists_conjWord (MonoidHom.id G)
      Function.surjective_id a hgen (i : G)
  let words : S → List (G × Bool) := fun i ↦
    if i = i₀ then [(1, true)] else Classical.choose (hex i)
  refine ⟨⟨S, hsymm, hclosure, i₀, rfl, words, ?_, ?_⟩⟩
  · intro i
    by_cases hi : i = i₀
    · subst i
      simp [words, i₀, ConjWord.conjWord]
    · change ConjWord.conjWord a
        (if i = i₀ then [(1, true)] else Classical.choose (hex i)) = i
      rw [if_neg hi]
      exact Classical.choose_spec (hex i)
  · simp [words]

/-- The decisive active-core contradiction for an already selected sequence
of visible exact torsion coordinates. -/
theorem false_of_shadow_of_visible_exact_packet
    (a : G) (haShadow : a ∈ opToHSShadowResidual G)
    (P : NormalGeneratorPacket G a)
    (m : ℕ) (hm : 0 < m)
    [∀ n, Nonempty (X n)]
    (rho : G →* NormMatrixCoronaUnitary X)
    (R : ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hR : QuotientGroup.mk R = rho a)
    (hpow : ∀ n, (R n) ^ m = 1)
    (hrank : ∀ n, 0 < (((R n : Matrix.unitaryGroup (X n) ℂ) :
      Matrix (X n) (X n) ℂ) - 1).rank)
    (C : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hC : ∀ g, QuotientGroup.mk (C g) = rho g)
    (hC1 : ∀ n, C 1 n = 1) : False := by
  classical
  let matrixWords : ∀ n, P.S →
      List (Matrix.unitaryGroup (X n) ℂ × Bool) := fun n i ↦
    (P.words i).map fun p ↦ (C p.1 n, p.2)
  let W : ∀ n, P.S → Matrix.unitaryGroup (X n) ℂ := fun n ↦
    TorsionActiveCore.conjugateWordPacket (R n) (matrixWords n)
  have hmark (n : ℕ) : W n P.mark = R n := by
    rw [show W n P.mark = TorsionActiveCore.conjugateWord (R n)
      (matrixWords n P.mark) by rfl]
    rw [show matrixWords n P.mark = [(1, true)] by
      simp [matrixWords, P.mark_word, hC1]]
    simp [TorsionActiveCore.conjugateWord, TorsionActiveCore.conjugateFactor]
  have hW : ∀ i : P.S, QuotientGroup.mk (fun n ↦ W n i) = rho i := by
    intro i
    exact quotient_mk_conjugateWordPacket P.S a P.words P.word_value rho
      R hR C hC i
  have hrespect :
      ActiveCoreAlmostRepresentation.AmbientWordsRespectGroup P.S W :=
    ambientWordsRespectGroup_of_corona P.S rho W hW
  have hcore : ∀ n,
      0 < Fintype.card (TorsionActiveCore.activeCoreModel (W n)) := by
    intro n
    rw [TorsionActiveCore.card_activeCoreModel,
      TorsionActiveCore.finrank_activeEuclideanSubspace]
    exact (hrank n).trans_le
      (TorsionActiveCore.rank_le_finrank_activeSubspace_of_eq
        (W n) (R n) P.mark (hmark n))
  let B : OpAlmostRepresentation G :=
    ActiveCoreAlmostRepresentation.compressedAlmostRepresentation
      P.S P.generates P.symmetric a P.mark P.mark_value W hcore hrespect
  have hlength (n : ℕ) :
      TorsionActiveCore.totalWordLength (matrixWords n) =
        ∑ i : P.S, (P.words i).length := by
    simp [TorsionActiveCore.totalWordLength, matrixWords]
  have hgap (n : ℕ) :
      1 ≤ (m : ℝ) ^ 2 *
          ((∑ i : P.S, (P.words i).length : ℕ) : ℝ) *
        hsNormSq (TorsionActiveCore.activeCoreModel (W n))
          (((TorsionActiveCore.activeCoreModelMatrix (W n) P.mark :
              Matrix.unitaryGroup (TorsionActiveCore.activeCoreModel (W n)) ℂ) :
            Matrix (TorsionActiveCore.activeCoreModel (W n))
              (TorsionActiveCore.activeCoreModel (W n)) ℂ) - 1) := by
    have hq := (FiniteOrderRankMass.activeCore_reblocking_dimension_and_hsGap
      (R n) (matrixWords n) P.mark (hmark n) m hm (hpow n) (hrank n)).2
    rw [hlength] at hq
    simpa [W] using hq
  have hL : 0 < ∑ i : P.S, (P.words i).length := by
    have hone : 1 ≤ ∑ i : P.S, (P.words i).length := by
      have hsingle := Finset.single_le_sum
        (s := Finset.univ) (f := fun i : P.S ↦ (P.words i).length)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ P.mark)
      simpa [P.mark_word] using hsingle
    exact Nat.zero_lt_of_lt hone
  let c : ℝ := (m : ℝ) ^ 2 *
    ((∑ i : P.S, (P.words i).length : ℕ) : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : ((U : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le Filter.cofinite
  have hkill := (mem_opToHSShadowResidual_iff a).mp haShadow B U hcof
  let A := KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B
  have hnull : (fun n ↦ A.map n a) ∈
      nullUnitarySubgroup U A.model A.modelNonempty := by
    exact (@QuotientGroup.eq_one_iff _ _
      (nullUnitarySubgroup U A.model A.modelNonempty) _
      (fun n ↦ A.map n a)).mp hkill
  have heps : 0 < (2 * c)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) hc)
  have hev := hnull ((2 * c)⁻¹) heps
  obtain ⟨n, hn⟩ := hev.exists
  change hsLengthSq (B.model n) (B.map n a) < (2 * c)⁻¹ at hn
  rw [hsLengthSq] at hn
  have hn' := hn
  have hg := hgap n
  have hmarkB := ActiveCoreAlmostRepresentation.compressedAlmostRepresentation_map_mark_model
    P.S P.generates P.symmetric a P.mark P.mark_value W hcore hrespect n
  rw [← hmarkB] at hg
  change 1 ≤ c * hsNormSq (B.model n)
      (((B.map n a : Matrix.unitaryGroup (B.model n) ℂ) :
        Matrix (B.model n) (B.model n) ℂ) - 1) at hg
  have hcne : 2 * c ≠ 0 := ne_of_gt (mul_pos (by norm_num) hc)
  have hinv : (2 * c)⁻¹ = 1 / (2 * c) := by rw [one_div]
  rw [hinv] at hn'
  have := hsNormSq_nonneg (B.model n)
    (((B.map n a : Matrix.unitaryGroup (B.model n) ℂ) :
      Matrix (B.model n) (B.model n) ℂ) - 1)
  field_simp [hcne] at hn'
  nlinarith

end

end FiniteOrderNormalGenerator
end GroupApproximation
