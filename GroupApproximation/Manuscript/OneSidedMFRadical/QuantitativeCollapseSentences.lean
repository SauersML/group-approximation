import GroupApproximation.Manuscript.OneSidedMFRadical.QuantitativeCollapse
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed proof of `prop:linear-collapse`, sentence by sentence

`non_mf_groups_exist.tex`, the proof of Proposition `prop:linear-collapse` and
the consequence paragraph that follows it.

`Manuscript/OneSidedMFRadical/QuantitativeCollapse.lean` carries the printed
*statement*, its converse and its two consequences as closed propositions.  This
module carries the printed *proof*: one `manuscriptSentence_*` lemma per printed
sentence, each proved from the four landed modules of this lane.  No new
mathematics is introduced here; where a printed sentence is an internal step of
the landed proof, the lemma states that step in the general form the sentence
asserts.

Two places where the Lean is deliberately not a literal transcription, both
recorded in the individual docstrings:

* the printed word estimate is `‖a(U) - 1‖ ≤ |a| · D(U)`, with `|a|` the word
  length.  `manuscriptSentence_wordLengthBound` gives a constant produced by the
  free-group induction and does not claim it is the length of any particular
  spelling; the printed argument uses only that some such constant exists;
* the printed sentence about the space of marked groups asserts that a certain
  set is open and closed.  `manuscriptSentence_markedGroupsSatisfyingRelations`
  carries only the mathematical content used, that every group in that set has
  the property.  The topology on the space of marked groups is not formalized
  anywhere in this development and no openness claim is made.

The remark about the two-generated group `Q` of `thm:torsion-free`, printed at
the end of the same paragraph, needs Theorem 5 and is not carried here.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace QuantitativeCollapseSentences

open Matrix Filter
open QuantitativeCollapse
open scoped Matrix.Norms.L2Operator
open scoped commutatorElement

/-! ## Sentence 1: the group is perfect -/

/-- **`prop:linear-collapse`, printed sentence.**

> a nontrivial abelianization of a finitely generated group has a nontrivial
> finite quotient

Stated in the printed direction.  The landed carrier is the contrapositive
`subsingleton_of_finite_targets_trivial`, whose proof is the structure theorem
for finitely generated abelian groups. -/
theorem manuscriptSentence_fgAbelianHasFiniteQuotient
    (A : Type) [CommGroup A] [Group.FG A] (hA : ¬ Subsingleton A) :
    ∃ (B : Type) (_ : Group B) (_ : Finite B) (φ : A →* B) (a : A), φ a ≠ 1 := by
  by_contra hcon
  refine hA (subsingleton_of_finite_targets_trivial A ?_)
  intro B _ _ φ a
  by_contra hne
  exact hcon ⟨B, ‹Group B›, ‹Finite B›, φ, a, hne⟩

/-- **`prop:linear-collapse`, printed sentence.**

> and finite groups are MF

The repository's `isOperatorMF_of_finite_standard`, transported to the literal
Carrión--Dadarlat--Eckhardt predicate. -/
theorem manuscriptSentence_finiteGroupsAreMF (B : Type) [Group B] [Finite B] :
    IsCDEOperatorMF B := by
  haveI : Countable B := Finite.to_countable
  exact (isCDEOperatorMF_iff_isOperatorMF B).mpr (isOperatorMF_of_finite_standard B)

/-- **`prop:linear-collapse`, printed sentence.**

> The group `G` is perfect.

The two preceding sentences are the proof: a nontrivial abelianization would
give a nontrivial finite quotient, and finite groups are MF. -/
theorem manuscriptSentence_perfect (G : Type) [Group G] [Group.FG G]
    (h : ∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1) :
    commutator G = ⊤ :=
  commutator_eq_top_of_mfTargets_trivial G h

/-! ## Sentences 2 and 3: the commutator words and the relations `w_i` -/

/-- **`prop:linear-collapse`, printed sentence.**

> So there are words `a_{ik}, b_{ik} ∈ F_m` with
> `g_i = ∏_{k=1}^{q_i} [a_{ik}(g₁,…,g_m), b_{ik}(g₁,…,g_m)]` for `1 ≤ i ≤ m`.

The pairs `(a_{ik}, b_{ik})` are carried as a list, so `q_i` is its length. -/
theorem manuscriptSentence_generatorsAreCommutatorProducts
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hperf : commutator G = ⊤) :
    ∃ l : Fin m → List (FreeGroup (Fin m) × FreeGroup (Fin m)),
      ∀ i, FreeGroup.lift g (((l i).map fun q ↦ ⁅q.1, q.2⁆).prod) = g i :=
  exists_commutatorWords g hgen hperf

/-- **`prop:linear-collapse`, printed sentence.**

> and the words `w_i = x_i⁻¹ ∏_{k=1}^{q_i} [a_{ik}, b_{ik}]` are relations of
> `G`. -/
theorem manuscriptSentence_relatorWords
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (l : Fin m → List (FreeGroup (Fin m) × FreeGroup (Fin m)))
    (hl : ∀ i, FreeGroup.lift g (((l i).map fun q ↦ ⁅q.1, q.2⁆).prod) = g i) (i : Fin m) :
    FreeGroup.lift g ((FreeGroup.of i)⁻¹ * ((l i).map fun q ↦ ⁅q.1, q.2⁆).prod) = 1 := by
  rw [map_mul, map_inv, FreeGroup.lift_apply_of, hl i, inv_mul_cancel]

/-! ## Sentence 4: the generator defect `D(U)` -/

/-- **`prop:linear-collapse`, printed sentence.**

> For a tuple `U = (U₁,…,U_m)` of unitaries put `D(U) = max_i ‖U_i - 1‖`.

The two clauses are what "maximum" is used for in the printed proof: it
dominates every generator defect, and it is the least such bound. -/
theorem manuscriptSentence_generatorDefect {m : ℕ} [Nonempty (Fin m)] (Y : FiniteModel)
    (U : Fin m → Matrix.unitaryGroup Y ℂ) :
    (∀ i, opLength Y (U i)
        ≤ Finset.univ.sup' Finset.univ_nonempty fun j ↦ opLength Y (U j)) ∧
      ∀ c : ℝ, (∀ i, opLength Y (U i) ≤ c) →
        (Finset.univ.sup' Finset.univ_nonempty fun j ↦ opLength Y (U j)) ≤ c := by
  constructor
  · intro i
    exact Finset.le_sup' (fun j ↦ opLength Y (U j)) (Finset.mem_univ i)
  · intro c hc
    exact Finset.sup'_le Finset.univ_nonempty (fun j ↦ opLength Y (U j)) fun j _ ↦ hc j

/-! ## Sentences 5, 6 and 7: the two elementary estimates -/

/-- **`prop:linear-collapse`, printed sentence.**

> A word `a` of length `|a|` has `‖a(U) - 1‖ ≤ |a| · D(U)`.

The constant is produced by the free-group induction, so it is the length of
whatever spelling the induction meets; no minimality over spellings is claimed,
and the printed argument uses only that some constant depending on the word
alone exists. -/
theorem manuscriptSentence_wordLengthBound {m : ℕ} (a : FreeGroup (Fin m)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (Y : FiniteModel) (U : Fin m → Matrix.unitaryGroup Y ℂ) (t : ℝ),
        (∀ i, opLength Y (U i) ≤ t) →
          opLength Y (FreeGroup.lift U a) ≤ L * t :=
  exists_word_bound a

/-- **`prop:linear-collapse`, printed sentence.**

> and unitaries `A, B` satisfy `‖[A,B] - 1‖ = ‖AB - BA‖ ≤ 2‖A - 1‖ ‖B - 1‖`.

Both halves of the printed display: the equality and the estimate. -/
theorem manuscriptSentence_commutatorEstimate (Y : FiniteModel)
    (A B : Matrix.unitaryGroup Y ℂ) :
    opLength Y ⁅A, B⁆
        = ‖(A : Matrix Y Y ℂ) * (B : Matrix Y Y ℂ)
            - (B : Matrix Y Y ℂ) * (A : Matrix Y Y ℂ)‖ ∧
      opLength Y ⁅A, B⁆ ≤ 2 * (opLength Y A * opLength Y B) :=
  ⟨CliffordBSAmenableMF.opLength_commutator Y A B, opLength_commutator_le Y A B⟩

/-- **`prop:linear-collapse`, printed sentence.**

> since `AB - BA = (A-1)(B-1) - (B-1)(A-1)`.

The identity holds in any ring; unitarity is used only afterwards, to discard
the factor `(BA)*`. -/
theorem manuscriptSentence_commutatorIdentity {Y : FiniteModel} (A B : Matrix Y Y ℂ) :
    A * B - B * A = (A - 1) * (B - 1) - (B - 1) * (A - 1) := by
  noncomm_ring

/-! ## Sentence 8: the bootstrap inequality `eq:bootstrap` -/

/-- **`prop:linear-collapse`, printed sentence.**

> So there is a constant `B₀`, determined by the chosen words, with
> `D(U) ≤ max_i ‖w_i(U) - 1‖ + B₀ · D(U)²`.  (`eq:bootstrap`)

The printed maxima are carried by the bound variables `t` and `δ`, exactly as in
`CollapseInequality`. -/
theorem manuscriptSentence_bootstrap {m : ℕ}
    (w : Fin m → FreeGroup (Fin m))
    (l : Fin m → List (FreeGroup (Fin m) × FreeGroup (Fin m)))
    (hw : ∀ i, w i = (FreeGroup.of i)⁻¹ * ((l i).map fun q ↦ ⁅q.1, q.2⁆).prod) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (Y : FiniteModel) (U : Fin m → Matrix.unitaryGroup Y ℂ) (t δ : ℝ), 0 ≤ t →
        (∀ j, opLength Y (U j) ≤ t) →
        (∀ j, opLength Y (FreeGroup.lift U (w j)) ≤ δ) →
          ∀ i, opLength Y (U i) ≤ δ + B * t ^ 2 :=
  exists_collapse_constant w l hw

/-! ## Sentence 9: the enumeration of the relations -/

/-- **`prop:linear-collapse`, printed sentence.**

> Enumerate the relations of `G` as `r₁, r₂, …` with `w₁,…,w_m` first, and put
> `R_n = {r₁,…,r_n}`.

Stated for an arbitrary predicate, since the only property of "being a relation"
the printed argument uses is that the words carrying it form a countable set.
The three clauses are what the enumeration is for: the `w_i` are in every stage,
every member of every stage carries the predicate, and every word carrying it
eventually appears. -/
theorem manuscriptSentence_relationEnumeration {m : ℕ}
    (P : FreeGroup (Fin m) → Prop) (w : Fin m → FreeGroup (Fin m)) (hw : ∀ i, P (w i)) :
    ∃ R : ℕ → Finset (FreeGroup (Fin m)),
      (∀ n (i : Fin m), w i ∈ R n) ∧
      (∀ n, ∀ r ∈ R n, P r) ∧
      (∀ r : FreeGroup (Fin m), P r → ∀ᶠ n in Filter.atTop, r ∈ R n) := by
  classical
  obtain ⟨enum, henum⟩ := exists_surjective_nat (FreeGroup (Fin m))
  refine ⟨fun n ↦ Finset.image w Finset.univ ∪
    ((Finset.range (n + 1)).image enum).filter (fun r ↦ P r), ?_, ?_, ?_⟩
  · intro n i
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · intro n r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
      exact hw i
    · exact (Finset.mem_filter.mp hr).2
  · intro r hr
    obtain ⟨k, hk⟩ := henum r
    rw [Filter.eventually_atTop]
    refine ⟨k, fun n hn ↦ ?_⟩
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, hr⟩)
    rw [← hk]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

/-! ## Sentences 10 and 11: the counterexample tuples and their vanishing defects -/

/-- **`prop:linear-collapse`, printed sentence.**

> If no `R_n` works with the constant `n`, there are `d_n` and tuples `U⁽ⁿ⁾` in
> `U(d_n)` with `D(U⁽ⁿ⁾) > n δ_n`, where
> `δ_n = max_{r ∈ R_n} ‖r(U⁽ⁿ⁾) - 1‖`.

The printed maximum `δ_n` is the bound variable `δ`, and the printed `d_n ≥ 1`
comes out of the failure because `CollapseInequality` quantifies over `d ≥ 1`. -/
theorem manuscriptSentence_counterexampleTuples {m : ℕ}
    (s : Finset (FreeGroup (Fin m))) (C : ℝ) (h : ¬ CollapseInequality m s C) :
    ∃ (d : ℕ) (U : Fin m → Matrix.unitaryGroup (naturalFiniteModel d) ℂ)
      (δ : ℝ) (i : Fin m),
      1 ≤ d ∧ (∀ r ∈ s, opLength (naturalFiniteModel d) (FreeGroup.lift U r) ≤ δ) ∧
        C * δ < opLength (naturalFiniteModel d) (U i) := by
  by_contra hcon
  refine h (collapseInequality_of_model ?_)
  intro d hd U δ hU i
  by_contra hlt
  exact hcon ⟨d, U, δ, i, hd, hU, not_le.mp hlt⟩

/-- **`prop:linear-collapse`, printed sentence.**

> Since `D(U⁽ⁿ⁾) ≤ 2`, `δ_n → 0`.

The bound `D(U⁽ⁿ⁾) ≤ 2` is `opLength_le_two`; the sentence itself is the
elementary consequence, stated for arbitrary real sequences. -/
theorem manuscriptSentence_relationDefectsVanish (δ D : ℕ → ℝ)
    (hlt : ∀ n : ℕ, ((n : ℝ) + 1) * δ n < D n) (hD : ∀ n : ℕ, D n ≤ 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, δ n < ε := by
  intro ε hε
  obtain ⟨N0, hN0⟩ := Archimedean.arch (2 : ℝ) hε
  rw [nsmul_eq_mul] at hN0
  rw [Filter.eventually_atTop]
  refine ⟨N0, fun n hn ↦ ?_⟩
  have hcast : (N0 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hden : (2 : ℝ) < ((n : ℝ) + 1) * ε := by
    nlinarith [hN0, hε, mul_nonneg (sub_nonneg.mpr hcast) hε.le]
  by_contra hcc
  have hge : ε ≤ δ n := not_lt.mp hcc
  have hmul : ((n : ℝ) + 1) * ε ≤ ((n : ℝ) + 1) * δ n :=
    mul_le_mul_of_nonneg_left hge (by positivity)
  have h1 := hlt n
  have h2 := hD n
  linarith

/-- The bound the previous sentence rests on: a unitary is at operator-norm
distance at most `2` from the identity. -/
theorem manuscriptSentence_defectBoundedByTwo (Y : FiniteModel) [Nonempty Y]
    (u : Matrix.unitaryGroup Y ℂ) : opLength Y u ≤ 2 :=
  opLength_le_two Y u

/-! ## Sentences 12 and 13: the corona homomorphism and its triviality -/

/-- **`prop:linear-collapse`, printed sentence.**

> so `g_i ↦ [U_i⁽ⁿ⁾]_n` is a homomorphism from `G` to the unitary group of
> `∏_n M_{d_n}(ℂ) / ⊕_n M_{d_n}(ℂ)`.

The hypothesis is exactly the printed "the relation defects tend to zero": every
relation of `G` maps to a null sequence. -/
theorem manuscriptSentence_coronaHomomorphism
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (X : ℕ → FiniteModel) (u : Fin m → (∀ n, Matrix.unitaryGroup (X n) ℂ))
    (hrel : ∀ r : FreeGroup (Fin m), FreeGroup.lift g r = 1 →
      FreeGroup.lift u r ∈ nullCofiniteOpSubgroup X) :
    ∃ θ : G →* NormMatrixCoronaUnitary X,
      ∀ i, θ (g i) = QuotientGroup.mk (u i) :=
  exists_coronaHom g hgen X u hrel

/-- **`prop:linear-collapse`, printed sentence.**

> trivial by hypothesis; so `D(U⁽ⁿ⁾) → 0`.

Triviality of the corona homomorphism is applied to its image subgroup, which is
countable because a marked group is, and MF because it embeds in the corona; the
conclusion is the printed convergence, uniformly in the generator index. -/
theorem manuscriptSentence_generatorDefectsVanish
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hkill : ∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (u : Fin m → (∀ n, Matrix.unitaryGroup (X n) ℂ))
    (hrel : ∀ r : FreeGroup (Fin m), FreeGroup.lift g r = 1 →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.cofinite,
        opLength (X n) (FreeGroup.lift (fun i ↦ u i n) r) < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.cofinite, ∀ i, opLength (X n) (u i n) < ε :=
  fun ε hε ↦ Filter.eventually_all.mpr fun i ↦
    generators_tendsto_one g hgen hkill X hX u hrel i ε hε

/-! ## Sentence 14: the bootstrap inequality is violated -/

/-- **`prop:linear-collapse`, printed sentence.**

> For `n ≥ m`, the inequality `eq:bootstrap` gives
> `D(U⁽ⁿ⁾) ≤ δ_n + B₀ D(U⁽ⁿ⁾)²`, and division by `D(U⁽ⁿ⁾)` gives
> `1 ≤ 1/n + B₀ D(U⁽ⁿ⁾)`, which fails for large `n`.

The division is carried as the arithmetic fact it produces: with the generator
defect positive, the bootstrap inequality, the printed
`δ_n < D(U⁽ⁿ⁾)/n`, and a small enough `B₀ · D(U⁽ⁿ⁾)` are jointly
contradictory. -/
theorem manuscriptSentence_bootstrapContradiction {D δ B : ℝ}
    (hD : 0 < D) (hboot : D ≤ δ + B * D ^ 2) (hδ : 2 * δ < D) (hBD : B * D < 1 / 2) :
    False := by
  have hprod : B * D ^ 2 < (1 / 2) * D := by
    calc B * D ^ 2 = (B * D) * D := by ring
      _ < (1 / 2) * D := mul_lt_mul_of_pos_right hBD hD
  linarith

/-! ## Sentences 15, 16 and 17: the converse -/

/-- **`prop:linear-collapse`, printed sentence.**

> Conversely, a corona homomorphism has unitary coordinate lifts whose relation
> defects tend to zero. -/
theorem manuscriptSentence_coronaLiftsHaveVanishingDefects
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    {s : Finset (FreeGroup (Fin m))} (hrel : ∀ r ∈ s, FreeGroup.lift g r = 1)
    (X : ℕ → FiniteModel) (h : G →* NormMatrixCoronaUnitary X) :
    ∃ u : Fin m → (∀ n, Matrix.unitaryGroup (X n) ℂ),
      (∀ i, QuotientGroup.mk' (nullCofiniteOpSubgroup X) (u i) = h (g i)) ∧
      ∀ r ∈ s, FreeGroup.lift u r ∈ nullCofiniteOpSubgroup X := by
  classical
  have hlift : ∀ i, ∃ v : ∀ n, Matrix.unitaryGroup (X n) ℂ,
      QuotientGroup.mk' (nullCofiniteOpSubgroup X) v = h (g i) :=
    fun i ↦ QuotientGroup.mk_surjective _
  choose u hu using hlift
  refine ⟨u, hu, ?_⟩
  intro r hr
  rw [← QuotientGroup.eq_one_iff]
  have h1 := lift_hom_comp (QuotientGroup.mk' (nullCofiniteOpSubgroup X)) u r
  have h2 := lift_hom_comp h g r
  rw [hrel r hr, map_one] at h2
  have h3 : QuotientGroup.mk' (nullCofiniteOpSubgroup X) (FreeGroup.lift u r) = 1 := by
    rw [h1]
    simp only [hu]
    rw [← h2]
  exact h3

/-- **`prop:linear-collapse`, printed sentence.**

> so the displayed inequality forces every generator lift to the identity, and
> the homomorphism is trivial. -/
theorem manuscriptSentence_inequalityKillsCorona
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    {s : Finset (FreeGroup (Fin m))} {C : ℝ}
    (hrel : ∀ r ∈ s, FreeGroup.lift g r = 1) (hineq : CollapseInequality m s C)
    (dd : ℕ → ℕ) (hdd : ∀ n, 0 < dd n)
    (h : G →* NormMatrixCoronaUnitary (fun n ↦ naturalFiniteModel (dd n))) :
    ∀ x : G, h x = 1 := by
  have hgens := generators_eq_one_of_collapseInequality g hrel hineq dd hdd h
  have hker : Subgroup.closure (Set.range g) ≤ h.ker := by
    rw [Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact MonoidHom.mem_ker.mpr (hgens i)
  rw [hgen] at hker
  intro x
  exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x))

/-- **`prop:linear-collapse`, printed sentence.**

> Lemma `prop:mf-residual-calculus` extends this to every homomorphism to an MF
> group.

This is where countability of `G`, assumed in the printed converse, is spent:
`manuscriptFullRadicalKillsMFTargets` needs it, and the step producing the full
radical from the inequality does not. -/
theorem manuscriptSentence_residualCalculusExtends
    (G : Type) [Group G] [Countable G] (hfull : manuscriptCoronaMFResidual G = ⊤)
    (M : Type) [Group M] [Countable M] (hMF : IsCDEOperatorMF M) (f : G →* M) (x : G) :
    f x = 1 :=
  manuscriptFullRadicalKillsMFTargets (G := G) (M := M) hfull
    ((isCDEOperatorMF_iff_isOperatorMF M).mp hMF) f x

/-- The half of the converse that the previous sentence is applied to: the
inequality forces the printed MF radical to be everything. -/
theorem manuscriptSentence_inequalityGivesFullRadical
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    {s : Finset (FreeGroup (Fin m))} {C : ℝ}
    (hrel : ∀ r ∈ s, FreeGroup.lift g r = 1) (hineq : CollapseInequality m s C) :
    manuscriptCoronaMFResidual G = ⊤ :=
  manuscriptCoronaMFResidual_eq_top_of_collapseInequality g hgen hrel hineq

/-! ## The consequence paragraph -/

/-- **The consequence paragraph, printed sentences.**

> With `r₁,…,r_s` as in Proposition `prop:linear-collapse`, put
> `P = ⟨x₁,…,x_m | r₁,…,r_s⟩`.  The inequality holds verbatim for `P`, so every
> finitely generated group all of whose homomorphisms to MF groups are trivial
> is a quotient of a finitely presented group with the same property and the
> same number of generators.

"The same number of generators" is the `Fin m` shared by `G` and `P`; the
surjection carries `PresentedGroup.of i` to `g i`. -/
theorem manuscriptSentence_presentedCover
    (G : Type) [Group G] (m : ℕ) (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hkill : ∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1) :
    ∃ s : Finset (FreeGroup (Fin m)),
      (∀ r ∈ s, FreeGroup.lift g r = 1) ∧
      (∃ φ : PresentedGroup (↑s : Set (FreeGroup (Fin m))) →* G,
          Function.Surjective φ ∧ ∀ i, φ (PresentedGroup.of i) = g i) ∧
      (∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
        ∀ (f : PresentedGroup (↑s : Set (FreeGroup (Fin m))) →* M)
          (x : PresentedGroup (↑s : Set (FreeGroup (Fin m)))), f x = 1) :=
  manuscriptLinearCollapseCover G m g hgen hkill

/-- **The consequence paragraph, printed sentence.**

> The set of `m`-marked groups satisfying `r₁ = ⋯ = r_s = 1` is open and closed
> in the space of marked groups, and every group in it has the property; so the
> property is open.

Only the middle clause is carried: every countable `m`-marked group satisfying
the relations again kills every homomorphism to a countable MF group.  The
space of marked groups, its topology, and the openness and closedness claims are
not formalized anywhere in this development, and nothing here asserts them. -/
theorem manuscriptSentence_markedGroupsSatisfyingRelations
    (G : Type) [Group G] (m : ℕ) (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hkill : ∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1) :
    ∃ (s : Finset (FreeGroup (Fin m))) (C : ℝ),
      0 < C ∧ (∀ r ∈ s, FreeGroup.lift g r = 1) ∧
        ∀ (H : Type) [Group H] [Countable H] (h : Fin m → H),
          Subgroup.closure (Set.range h) = ⊤ →
          (∀ r ∈ s, FreeGroup.lift h r = 1) →
          ∀ (M : Type) [Group M] [Countable M],
            IsCDEOperatorMF M → ∀ (f : H →* M) (x : H), f x = 1 :=
  manuscriptLinearCollapseMarkedGroups G m g hgen hkill

end QuantitativeCollapseSentences
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.OneSidedMFRadical.QuantitativeCollapseSentences

#audit_axioms manuscriptSentence_fgAbelianHasFiniteQuotient
#audit_axioms manuscriptSentence_finiteGroupsAreMF
#audit_axioms manuscriptSentence_perfect
#audit_axioms manuscriptSentence_generatorsAreCommutatorProducts
#audit_axioms manuscriptSentence_relatorWords
#audit_axioms manuscriptSentence_generatorDefect
#audit_axioms manuscriptSentence_wordLengthBound
#audit_axioms manuscriptSentence_commutatorEstimate
#audit_axioms manuscriptSentence_commutatorIdentity
#audit_axioms manuscriptSentence_bootstrap
#audit_axioms manuscriptSentence_relationEnumeration
#audit_axioms manuscriptSentence_counterexampleTuples
#audit_axioms manuscriptSentence_relationDefectsVanish
#audit_axioms manuscriptSentence_defectBoundedByTwo
#audit_axioms manuscriptSentence_coronaHomomorphism
#audit_axioms manuscriptSentence_generatorDefectsVanish
#audit_axioms manuscriptSentence_bootstrapContradiction
#audit_axioms manuscriptSentence_coronaLiftsHaveVanishingDefects
#audit_axioms manuscriptSentence_inequalityKillsCorona
#audit_axioms manuscriptSentence_residualCalculusExtends
#audit_axioms manuscriptSentence_inequalityGivesFullRadical
#audit_axioms manuscriptSentence_presentedCover
#audit_axioms manuscriptSentence_markedGroupsSatisfyingRelations
