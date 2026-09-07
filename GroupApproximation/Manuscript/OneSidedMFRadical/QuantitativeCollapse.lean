import GroupApproximation.Manuscript.OneSidedMFRadical.QuantitativeCollapseCorona
import GroupApproximation.Manuscript.OneSidedMFRadical.QuantitativeCollapseEstimates
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.PresentedGroup

/-!
# `prop:linear-collapse`: a full MF radical is a finite certificate

`non_mf_groups_exist.tex`, Proposition `prop:linear-collapse`, in the section
"A finite certificate", together with the two unlabelled consequences printed
immediately after its proof.

The printed statement.  Let `G = ⟨g₁,…,g_m⟩` be finitely generated and suppose
every homomorphism from `G` to an MF group is trivial.  Then there are finitely
many words `r₁,…,r_s` of the free group `F_m` with `r_j(g₁,…,g_m) = 1` in `G`,
and a constant `C`, such that all unitaries `U₁,…,U_m ∈ U(d)`, for every
`d ≥ 1`, satisfy

`max_i ‖U_i - 1‖ ≤ C · max_j ‖r_j(U₁,…,U_m) - 1‖`.

Conversely, if such words and such a constant exist and `G` is countable, then
every homomorphism from `G` to an MF group is trivial.

The printed maximum is carried here by a bound variable `δ`: the inequality
`CollapseInequality` reads "if every relation defect is at most `δ` then every
generator defect is at most `C · δ`", which is the same statement, avoids a
nonemptiness side condition on `Finset.sup'`, and is the form the converse
consumes.  The constant produced by the forward direction is positive, which
the printed statement does not claim and does not need.

## The proof, as printed

The group is perfect (`commutator_eq_top_of_mfTargets_trivial`), so each
generator is a product of commutators of words (`exists_commutatorWords`),
giving relations `w i = x_i⁻¹ ∏_k ⁅a_{ik}, b_{ik}⁆`.  The two elementary
unitary estimates give `eq:bootstrap`, `D(U) ≤ max_i ‖w_i(U) - 1‖ + B₀·D(U)²`,
as `exists_collapse_constant`.  If no finite family and constant worked, a
counterexample against the first `n` relations of an exhaustion, with constant
`n+1`, has vanishing relation defects, so it defines a corona homomorphism
(`generators_tendsto_one`) which the hypothesis kills; `eq:bootstrap` then gives
`1 < 1/(n+1) + B₀·D(U⁽ⁿ⁾)` for every `n`, which fails once `D(U⁽ⁿ⁾)` is small.

The converse runs through the printed MF radical: the inequality forces
`Rad_MF(G) = G` (`manuscriptCoronaMFResidual_eq_top_of_collapseInequality`), and
`prop:mf-residual-calculus`, in the form `manuscriptFullRadicalKillsMFTargets`,
extends that from corona homomorphisms to every homomorphism into an MF group.
That last step is where countability of `G` is spent, which is why the printed
converse assumes it.

## Endpoints

* `manuscriptLinearCollapse`, `manuscriptLinearCollapseConverse`
* `manuscriptLinearCollapseCover` — the finitely presented cover
  `P = ⟨x₁,…,x_m | r₁,…,r_s⟩` maps onto `G` and has the same property, on the
  same number of generators.
* `manuscriptLinearCollapseMarkedGroups` — every countable `m`-marked group
  satisfying `r₁ = ⋯ = r_s = 1` has the property.  This is the content of the
  printed openness sentence; the topology on the space of marked groups is not
  formalized here, and no claim about it is made.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace QuantitativeCollapse

open Matrix Filter
open scoped Matrix.Norms.L2Operator
open scoped commutatorElement

/-! ## The printed inequality -/

/-- **The collapse inequality** at a finite family of words `s` and a constant
`C`: in every matrix size `d ≥ 1`, a unitary tuple whose defects at the words of
`s` are all at most `δ` has every generator defect at most `C · δ`.

This is the printed maximum form
`max_i ‖U_i - 1‖ ≤ C · max_j ‖r_j(U) - 1‖` with the right-hand maximum named
`δ`; quantifying over `δ` avoids a nonemptiness side condition on
`Finset.sup'`, and it is the form the converse consumes.

The statement mentions only the words and the constant, not the group: that is
exactly why it transfers to the finitely presented cover and to every marked
group satisfying the same relations. -/
def CollapseInequality (m : ℕ) (s : Finset (FreeGroup (Fin m))) (C : ℝ) : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (U : Fin m → Matrix.unitaryGroup (Fin d) ℂ) (δ : ℝ),
    (∀ r ∈ s, ‖((FreeGroup.lift U r : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) - 1‖ ≤ δ) →
      ∀ i, ‖((U i : Matrix (Fin d) (Fin d) ℂ)) - 1‖ ≤ C * δ

/-- The collapse inequality read at the repository's model `M_d(ℂ)`. -/
theorem collapseInequality_model {m : ℕ} {s : Finset (FreeGroup (Fin m))} {C : ℝ}
    (h : CollapseInequality m s C) (d : ℕ) (hd : 1 ≤ d)
    (U : Fin m → Matrix.unitaryGroup (naturalFiniteModel d) ℂ) (δ : ℝ)
    (hU : ∀ r ∈ s, opLength (naturalFiniteModel d) (FreeGroup.lift U r) ≤ δ) :
    ∀ i, opLength (naturalFiniteModel d) (U i) ≤ C * δ :=
  h d hd U δ hU

/-- The collapse inequality is exactly its reading at `M_d(ℂ)`. -/
theorem collapseInequality_of_model {m : ℕ} {s : Finset (FreeGroup (Fin m))} {C : ℝ}
    (h : ∀ (d : ℕ), 1 ≤ d →
      ∀ (U : Fin m → Matrix.unitaryGroup (naturalFiniteModel d) ℂ) (δ : ℝ),
      (∀ r ∈ s, opLength (naturalFiniteModel d) (FreeGroup.lift U r) ≤ δ) →
        ∀ i, opLength (naturalFiniteModel d) (U i) ≤ C * δ) :
    CollapseInequality m s C :=
  fun d hd U δ hU ↦ h d hd U δ hU

/-! ## The printed statements -/

/-- **`prop:linear-collapse`, forward direction.**  A marked group killing every
homomorphism into a countable MF group satisfies a collapse inequality at a
finite family of its relations. -/
def PrintedLinearCollapse : Prop :=
  ∀ (G : Type) [Group G] (m : ℕ) (g : Fin m → G),
    Subgroup.closure (Set.range g) = ⊤ →
    (∀ (M : Type) [Group M] [Countable M],
        IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1) →
    ∃ (s : Finset (FreeGroup (Fin m))) (C : ℝ),
      0 < C ∧ (∀ r ∈ s, FreeGroup.lift g r = 1) ∧ CollapseInequality m s C

/-- **`prop:linear-collapse`, converse.**  A collapse inequality at a finite
family of relations of a *countable* marked group kills every homomorphism into
a countable MF group. -/
def PrintedLinearCollapseConverse : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (m : ℕ) (g : Fin m → G),
    Subgroup.closure (Set.range g) = ⊤ →
    ∀ (s : Finset (FreeGroup (Fin m))) (C : ℝ),
      (∀ r ∈ s, FreeGroup.lift g r = 1) → CollapseInequality m s C →
      ∀ (M : Type) [Group M] [Countable M],
        IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1

/-- **The first printed consequence.**  Every finitely generated group killing
all its homomorphisms into countable MF groups is a quotient, on the same
generators, of a finitely presented group with the same property. -/
def PrintedLinearCollapseCover : Prop :=
  ∀ (G : Type) [Group G] (m : ℕ) (g : Fin m → G),
    Subgroup.closure (Set.range g) = ⊤ →
    (∀ (M : Type) [Group M] [Countable M],
        IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1) →
    ∃ s : Finset (FreeGroup (Fin m)),
      (∀ r ∈ s, FreeGroup.lift g r = 1) ∧
      (∃ φ : PresentedGroup (↑s : Set (FreeGroup (Fin m))) →* G,
          Function.Surjective φ ∧ ∀ i, φ (PresentedGroup.of i) = g i) ∧
      (∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
        ∀ (f : PresentedGroup (↑s : Set (FreeGroup (Fin m))) →* M)
          (x : PresentedGroup (↑s : Set (FreeGroup (Fin m)))), f x = 1)

/-- **The second printed consequence.**  The relations `r₁,…,r_s` produced by
`prop:linear-collapse` work for *every* countable `m`-marked group satisfying
them: each such group again kills every homomorphism into a countable MF group.

This is the content of the printed sentence that the set of `m`-marked groups
satisfying `r₁ = ⋯ = r_s = 1` consists of groups with the property.  The
topology on the space of marked groups is not formalized, and no openness claim
is made here. -/
def PrintedLinearCollapseMarkedGroups : Prop :=
  ∀ (G : Type) [Group G] (m : ℕ) (g : Fin m → G),
    Subgroup.closure (Set.range g) = ⊤ →
    (∀ (M : Type) [Group M] [Countable M],
        IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1) →
    ∃ (s : Finset (FreeGroup (Fin m))) (C : ℝ),
      0 < C ∧ (∀ r ∈ s, FreeGroup.lift g r = 1) ∧
        ∀ (H : Type) [Group H] [Countable H] (h : Fin m → H),
          Subgroup.closure (Set.range h) = ⊤ →
          (∀ r ∈ s, FreeGroup.lift h r = 1) →
          ∀ (M : Type) [Group M] [Countable M],
            IsCDEOperatorMF M → ∀ (f : H →* M) (x : H), f x = 1

/-! ## The forward direction -/

theorem manuscriptLinearCollapse : PrintedLinearCollapse := by
  classical
  intro G _ m g hgen hkill
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact ⟨∅, 1, one_pos, by simp, fun d _ U δ _ i ↦ i.elim0⟩
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hmpos
  haveI : Group.FG G := fg_of_marked g hgen
  haveI : Countable G := countable_of_marked g hgen
  have hperf : commutator G = ⊤ := commutator_eq_top_of_mfTargets_trivial G hkill
  obtain ⟨l, hl⟩ := exists_commutatorWords g hgen hperf
  obtain ⟨w, hwdef⟩ : ∃ w : Fin m → FreeGroup (Fin m),
      ∀ i, w i = (FreeGroup.of i)⁻¹ * ((l i).map fun q ↦ ⁅q.1, q.2⁆).prod :=
    ⟨_, fun i ↦ rfl⟩
  have hwrel : ∀ i, FreeGroup.lift g (w i) = 1 := by
    intro i
    rw [hwdef i, map_mul, map_inv, FreeGroup.lift_apply_of, hl i, inv_mul_cancel]
  obtain ⟨B, hB0, hBineq⟩ := exists_collapse_constant w l hwdef
  by_contra hno
  have hfail : ∀ (s : Finset (FreeGroup (Fin m))) (C : ℝ), 0 < C →
      (∀ r ∈ s, FreeGroup.lift g r = 1) → ¬ CollapseInequality m s C :=
    fun s C hC hrel hineq ↦ hno ⟨s, C, hC, hrel, hineq⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat (FreeGroup (Fin m))
  obtain ⟨R, hRW, hRenum, hRrel⟩ :
      ∃ R : ℕ → Finset (FreeGroup (Fin m)),
        (∀ n (i : Fin m), w i ∈ R n) ∧
        (∀ n k, k ≤ n → FreeGroup.lift g (enum k) = 1 → enum k ∈ R n) ∧
        (∀ n, ∀ r ∈ R n, FreeGroup.lift g r = 1) := by
    refine ⟨fun n ↦ Finset.image w Finset.univ ∪
      ((Finset.range (n + 1)).image enum).filter (fun r ↦ FreeGroup.lift g r = 1),
      ?_, ?_, ?_⟩
    · intro n i
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    · intro n k hkn hk1
      refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, hk1⟩)
      exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
    · intro n r hr
      rcases Finset.mem_union.mp hr with hr | hr
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
        exact hwrel i
      · exact (Finset.mem_filter.mp hr).2
  -- a counterexample against the first `n` relations, with constant `n + 1`
  have hstep : ∀ n : ℕ, ∃ (dn : ℕ) (U : Fin m → Matrix.unitaryGroup (naturalFiniteModel dn) ℂ)
      (δ : ℝ) (i : Fin m),
      1 ≤ dn ∧
      (∀ r ∈ R n, opLength (naturalFiniteModel dn) (FreeGroup.lift U r) ≤ δ) ∧
        ((n : ℝ) + 1) * δ < opLength (naturalFiniteModel dn) (U i) := by
    intro n
    by_contra hcon
    refine hfail (R n) ((n : ℝ) + 1) (by positivity) (hRrel n) (collapseInequality_of_model ?_)
    intro dn hdn U δ hU i
    by_contra hlt
    exact hcon ⟨dn, U, δ, i, hdn, hU, not_le.mp hlt⟩
  choose dseq Useq δseq iseq hdseq hUseq hgt using hstep
  have hNe : ∀ n, Nonempty (naturalFiniteModel (dseq n)) := fun n ↦
    Fin.pos_iff_nonempty.mp (hdseq n)
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℝ, ∀ n, D n =
      Finset.univ.sup' Finset.univ_nonempty
        (fun j ↦ opLength (naturalFiniteModel (dseq n)) (Useq n j)) := ⟨_, fun n ↦ rfl⟩
  have hDle : ∀ n j, opLength (naturalFiniteModel (dseq n)) (Useq n j) ≤ D n := by
    intro n j
    rw [hDdef n]
    exact Finset.le_sup'
      (fun j ↦ opLength (naturalFiniteModel (dseq n)) (Useq n j)) (Finset.mem_univ j)
  have hDsup : ∀ n (c : ℝ),
      (∀ j, opLength (naturalFiniteModel (dseq n)) (Useq n j) ≤ c) → D n ≤ c := by
    intro n c hc
    rw [hDdef n]
    exact Finset.sup'_le Finset.univ_nonempty
      (fun j ↦ opLength (naturalFiniteModel (dseq n)) (Useq n j)) fun j _ ↦ hc j
  have hδnn : ∀ n, 0 ≤ δseq n := by
    intro n
    exact le_trans (opLength_nonneg _ _)
      (hUseq n (w (Classical.arbitrary (Fin m))) (hRW n (Classical.arbitrary (Fin m))))
  have hDpos : ∀ n, 0 < D n := by
    intro n
    have h1 := hgt n
    have h2 := hDle n (iseq n)
    have h3 : (0 : ℝ) ≤ ((n : ℝ) + 1) * δseq n :=
      mul_nonneg (by positivity) (hδnn n)
    linarith
  have hDle2 : ∀ n, D n ≤ 2 := by
    intro n
    haveI := hNe n
    exact hDsup n 2 fun j ↦ opLength_le_two _ _
  have hdpos : ∀ n, 0 < Fintype.card (naturalFiniteModel (dseq n)) := by
    intro n
    haveI := hNe n
    exact Fintype.card_pos
  -- the relation defects vanish along the sequence
  have hrelvanish : ∀ r : FreeGroup (Fin m), FreeGroup.lift g r = 1 →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.cofinite,
        opLength (naturalFiniteModel (dseq n)) (FreeGroup.lift (fun i ↦ Useq n i) r) < ε := by
    intro r hr ε hε
    obtain ⟨k, hk⟩ := henum r
    obtain ⟨N0, hN0⟩ := Archimedean.arch (2 : ℝ) hε
    rw [nsmul_eq_mul] at hN0
    rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
    refine ⟨max k N0, fun n hn ↦ ?_⟩
    have hkn : k ≤ n := le_trans (le_max_left _ _) hn
    have hN0n : N0 ≤ n := le_trans (le_max_right _ _) hn
    have hmem : r ∈ R n := by
      rw [← hk]
      exact hRenum n k hkn (by rw [hk]; exact hr)
    have h1 : opLength (naturalFiniteModel (dseq n)) (FreeGroup.lift (Useq n) r) ≤ δseq n :=
      hUseq n r hmem
    have h2 : ((n : ℝ) + 1) * δseq n < D n :=
      lt_of_lt_of_le (hgt n) (hDle n (iseq n))
    have h3 : D n ≤ 2 := hDle2 n
    have hcast : (N0 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hN0n
    have hden : (2 : ℝ) < ((n : ℝ) + 1) * ε := by
      nlinarith [hN0, hε, mul_nonneg (sub_nonneg.mpr hcast) hε.le]
    have hδ : δseq n < ε := by
      by_contra hcc
      have hge : ε ≤ δseq n := not_lt.mp hcc
      have hmul : ((n : ℝ) + 1) * ε ≤ ((n : ℝ) + 1) * δseq n :=
        mul_le_mul_of_nonneg_left hge (by positivity)
      linarith
    exact lt_of_le_of_lt h1 hδ
  -- the corona homomorphism is trivial, so the generator defects vanish too
  have hgen1 := generators_tendsto_one g hgen hkill
    (fun n ↦ naturalFiniteModel (dseq n)) hdpos (fun i n ↦ Useq n i) hrelvanish
  have hall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.cofinite,
      ∀ i, opLength (naturalFiniteModel (dseq n)) (Useq n i) < ε :=
    fun ε hε ↦ Filter.eventually_all.mpr fun i ↦ hgen1 i ε hε
  -- and then `eq:bootstrap` is violated
  obtain ⟨ε0, hε0pos, hε0key⟩ : ∃ ε0 : ℝ, 0 < ε0 ∧ B * ε0 < 1 / 2 := by
    have hBp : (0 : ℝ) < 2 * (B + 1) := by linarith
    refine ⟨1 / (2 * (B + 1)), div_pos one_pos hBp, ?_⟩
    refine lt_of_mul_lt_mul_right ?_ hBp.le
    have h1 : B * (1 / (2 * (B + 1))) * (2 * (B + 1)) = B := by
      rw [mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hBp), mul_one]
    have h2 : (1 / 2 : ℝ) * (2 * (B + 1)) = B + 1 := by ring
    rw [h1, h2]
    linarith
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp
    (by rw [← Nat.cofinite_eq_atTop]; exact hall ε0 hε0pos)
  obtain ⟨n0, hn0N, hn0one⟩ : ∃ n0 : ℕ, N1 ≤ n0 ∧ 1 ≤ n0 :=
    ⟨max N1 1, le_max_left _ _, le_max_right _ _⟩
  have hDsmall : D n0 ≤ ε0 := hDsup n0 ε0 fun j ↦ (hN1 n0 hn0N j).le
  have hineq1 : ∀ i, opLength (naturalFiniteModel (dseq n0)) (Useq n0 i)
      ≤ δseq n0 + B * (D n0) ^ 2 :=
    hBineq (naturalFiniteModel (dseq n0)) (Useq n0) (D n0) (δseq n0) (hDpos n0).le
      (fun j ↦ hDle n0 j) (fun j ↦ hUseq n0 (w j) (hRW n0 j))
  have hDineq : D n0 ≤ δseq n0 + B * (D n0) ^ 2 := hDsup n0 _ hineq1
  have hgtn : ((n0 : ℝ) + 1) * δseq n0 < D n0 :=
    lt_of_lt_of_le (hgt n0) (hDle n0 (iseq n0))
  have h2δ : 2 * δseq n0 < D n0 := by
    have hcast : (2 : ℝ) ≤ (n0 : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hn0one
      linarith
    have := mul_le_mul_of_nonneg_right hcast (hδnn n0)
    linarith
  have hBDhalf : B * D n0 < 1 / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hDsmall hB0) hε0key
  have hprod : B * (D n0) ^ 2 < (1 / 2) * D n0 := by
    calc B * (D n0) ^ 2 = (B * D n0) * D n0 := by ring
      _ < (1 / 2) * D n0 := mul_lt_mul_of_pos_right hBDhalf (hDpos n0)
  linarith

/-! ## The converse -/

/-- The converse at a fixed corona: the collapse inequality forces every
generator's image in the corona to be trivial. -/
theorem generators_eq_one_of_collapseInequality
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    {s : Finset (FreeGroup (Fin m))} {C : ℝ}
    (hrel : ∀ r ∈ s, FreeGroup.lift g r = 1)
    (hineq : CollapseInequality m s C)
    (dd : ℕ → ℕ) (hdd : ∀ n, 0 < dd n)
    (h : G →* NormMatrixCoronaUnitary (fun n ↦ naturalFiniteModel (dd n))) :
    ∀ i, h (g i) = 1 := by
  classical
  have hlift : ∀ i, ∃ v : ∀ n, Matrix.unitaryGroup (naturalFiniteModel (dd n)) ℂ,
      (QuotientGroup.mk' (nullCofiniteOpSubgroup (fun n ↦ naturalFiniteModel (dd n))) v)
        = h (g i) := fun i ↦ QuotientGroup.mk_surjective _
  choose u hu using hlift
  have hnull : ∀ r ∈ s,
      FreeGroup.lift u r ∈
        nullCofiniteOpSubgroup (fun n ↦ naturalFiniteModel (dd n)) := by
    intro r hr
    rw [← QuotientGroup.eq_one_iff]
    have h1 := lift_hom_comp
      (QuotientGroup.mk' (nullCofiniteOpSubgroup (fun n ↦ naturalFiniteModel (dd n)))) u r
    have h2 := lift_hom_comp h g r
    rw [hrel r hr, map_one] at h2
    have h3 : (QuotientGroup.mk' (nullCofiniteOpSubgroup
        (fun n ↦ naturalFiniteModel (dd n)))) (FreeGroup.lift u r) = 1 := by
      rw [h1]
      simp only [hu]
      rw [← h2]
    exact h3
  intro i
  rw [← hu i, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  intro ε hε
  have hCpos : (0 : ℝ) < |C| + 1 := by positivity
  have hCne : |C| + 1 ≠ 0 := ne_of_gt hCpos
  have hεc : 0 < ε / (|C| + 1) := div_pos hε hCpos
  have hcancel : (|C| + 1) * (ε / (|C| + 1)) = ε := by field_simp
  have hlt : C * (ε / (|C| + 1)) < ε := by
    have hstep : C * (ε / (|C| + 1)) ≤ |C| * (ε / (|C| + 1)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hεc.le
    nlinarith [hcancel, hεc, hstep]
  have hev : ∀ᶠ n in Filter.cofinite, ∀ r ∈ s,
      opLength (naturalFiniteModel (dd n))
        (FreeGroup.lift (fun j ↦ u j n) r) ≤ ε / (|C| + 1) := by
    rw [Filter.eventually_all_finset]
    intro r hr
    filter_upwards [hnull r hr (ε / (|C| + 1)) hεc] with n hn
    rw [← lift_pi_apply (fun n ↦ naturalFiniteModel (dd n)) u r n]
    exact hn.le
  filter_upwards [hev] with n hn
  have happ : opLength (naturalFiniteModel (dd n)) (u i n) ≤ C * (ε / (|C| + 1)) :=
    hineq (dd n) (hdd n) (fun j ↦ u j n) (ε / (|C| + 1)) (fun r hr ↦ hn r hr) i
  exact lt_of_le_of_lt happ hlt

/-- **The collapse inequality forces a full MF radical.**  This is the first
half of the printed converse; countability of `G` is not needed for it. -/
theorem manuscriptCoronaMFResidual_eq_top_of_collapseInequality
    {G : Type} [Group G] {m : ℕ} (g : Fin m → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    {s : Finset (FreeGroup (Fin m))} {C : ℝ}
    (hrel : ∀ r ∈ s, FreeGroup.lift g r = 1)
    (hineq : CollapseInequality m s C) :
    manuscriptCoronaMFResidual G = ⊤ := by
  classical
  refine eq_top_iff.mpr fun x _ ↦ mem_manuscriptCoronaMFResidual_iff.mpr ?_
  intro d hd
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) := fun n ↦
    Fintype.card_pos_iff.mp (by simpa using hd n)
  intro rho
  have hgens := generators_eq_one_of_collapseInequality g hrel hineq d hd
    ((normMatrixCoronaUnitaryEquiv
      (fun n ↦ naturalFiniteModel (d n))).symm.toMonoidHom.comp rho)
  have hker : Subgroup.closure (Set.range g) ≤
      ((normMatrixCoronaUnitaryEquiv
        (fun n ↦ naturalFiniteModel (d n))).symm.toMonoidHom.comp rho).ker := by
    rw [Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact MonoidHom.mem_ker.mpr (hgens i)
  rw [hgen] at hker
  have hx := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x))
  apply (normMatrixCoronaUnitaryEquiv (fun n ↦ naturalFiniteModel (d n))).symm.injective
  rw [map_one]
  exact hx

theorem manuscriptLinearCollapseConverse : PrintedLinearCollapseConverse := by
  intro G _ _ m g hgen s C hrel hineq M _ _ hMF f x
  exact manuscriptFullRadicalKillsMFTargets (G := G) (M := M)
    (manuscriptCoronaMFResidual_eq_top_of_collapseInequality g hgen hrel hineq)
    ((isCDEOperatorMF_iff_isOperatorMF M).mp hMF) f x

/-! ## The two printed consequences -/

theorem manuscriptLinearCollapseMarkedGroups : PrintedLinearCollapseMarkedGroups := by
  intro G _ m g hgen hkill
  obtain ⟨s, C, hC, hrel, hineq⟩ := manuscriptLinearCollapse G m g hgen hkill
  refine ⟨s, C, hC, hrel, ?_⟩
  intro H _ _ h hHgen hHrel M _ _ hMF f x
  exact manuscriptLinearCollapseConverse H m h hHgen s C hHrel hineq M hMF f x

theorem manuscriptLinearCollapseCover : PrintedLinearCollapseCover := by
  classical
  intro G _ m g hgen hkill
  obtain ⟨s, C, -, hrel, hineq⟩ := manuscriptLinearCollapse G m g hgen hkill
  have hrelSet : ∀ r ∈ (↑s : Set (FreeGroup (Fin m))), FreeGroup.lift g r = 1 :=
    fun r hr ↦ hrel r (Finset.mem_coe.mp hr)
  haveI : Countable (PresentedGroup (↑s : Set (FreeGroup (Fin m)))) :=
    (PresentedGroup.mk_surjective _).countable
  have hrelP : ∀ r ∈ s, FreeGroup.lift
      (PresentedGroup.of : Fin m → PresentedGroup (↑s : Set (FreeGroup (Fin m)))) r = 1 := by
    intro r hr
    have h1 : FreeGroup.lift
        (PresentedGroup.of : Fin m → PresentedGroup (↑s : Set (FreeGroup (Fin m)))) r
        = PresentedGroup.mk (↑s : Set (FreeGroup (Fin m))) r :=
      (FreeGroup.lift_unique
        (f := (PresentedGroup.of : Fin m → PresentedGroup (↑s : Set (FreeGroup (Fin m)))))
        (PresentedGroup.mk (↑s : Set (FreeGroup (Fin m)))) (fun i ↦ rfl)).symm
    rw [h1]
    exact PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)
  refine ⟨s, hrel, ⟨PresentedGroup.toGroup hrelSet, ?_, fun i ↦ by simp⟩, ?_⟩
  · rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, by simp⟩
  · intro M _ _ hMF fM y
    exact manuscriptLinearCollapseConverse
      (PresentedGroup (↑s : Set (FreeGroup (Fin m)))) m PresentedGroup.of
      (PresentedGroup.closure_range_of _) s C hrelP hineq M hMF fM y

end QuantitativeCollapse
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.QuantitativeCollapse.manuscriptLinearCollapse

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.QuantitativeCollapse.manuscriptLinearCollapseConverse

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.QuantitativeCollapse.manuscriptLinearCollapseCover

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.QuantitativeCollapse.manuscriptLinearCollapseMarkedGroups
