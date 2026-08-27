import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
import GroupApproximation.Analysis.MFAlgebraMatrixAmplification
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.HyperlinearNonScalar
import GroupApproximation.Sofic.NormTraceGap
import GroupApproximation.Analysis.PolarLiftingGeneralCStar
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.HNNExtension
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Countable.Defs

/-!
# Sentence-level formalization: `lem:rf-regular` and `lem:reduced-products`

This file gives one Lean declaration per printed sentence of the `lem:rf-regular`
statement and proof, the setup paragraph preceding `thm:hnn-permanence`
(`eq:hnn`), and the two explanatory sentences following `lem:reduced-products`
in `mf_recognition_complexity.tex`.

The construction of `lem:rf-regular` is the *literal* printed argument: a
genuinely decreasing chain of finite-index normal subgroups `N_1 ≥ N_2 ≥ ⋯`
with trivial intersection, the exact left regular representation of each
finite quotient `G/N_k` (not the local-embedding route used by the repo's
generic `LEF` machinery), and the corona homomorphism / tracial state built
from that exact tower.  Once the tower is packaged as a
`RegularTraceWeakMFApproximation`, every subsequent step (the corona
homomorphism, its injectivity, the vanishing of the trace off the identity,
the separable generated subalgebra, and the final realization) reuses the
generic infrastructure already proved in `HNNCoronaConjugatorSentenceAudit`,
exactly as the repo's own `residuallyFinite_isRegularlyRealized` does for the
non-literal `LEF` route.

**Naming note.** `RegularTraceWeakMFApproximation`'s `cofiniteCStarCoronaHom`
and `cofiniteCStarCoronaHom_regularTrace` live in the sub-namespace
`RegularTraceWeakMFApproximation` opened inside
`HNNCoronaConjugatorSentenceAudit`, not in the top-level
`GroupApproximation.RegularTraceWeakMFApproximation` namespace where the
structure itself is declared.  So they must be called as fully-applied
functions (`RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom M`), never
via dot notation (`M.cofiniteCStarCoronaHom`), which resolves against the
wrong (structure-declaring) namespace and fails to find them.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Sentences

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open GroupApproximation.MFAlgebraMatrixAmplification
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## `lem:rf-regular`, sentence `2164704a2652`:
"Choose finite-index normal subgroups `N₁ ≥ N₂ ≥ ⋯` with trivial intersection,
and let `λ_k` be the left regular representation of `G/N_k`, of dimension
`d_k`." -/

section RfRegularTower

variable {G : Type} [Group G]

open scoped Classical in
/-- A finite-index normal subgroup separating a single element from `1`,
chosen so that `1` itself gets the trivial (finite-index, normal) subgroup. -/
noncomputable def rfChoice [Group.ResiduallyFinite G] (e : ℕ → G) (i : ℕ) :
    FiniteIndexNormalSubgroup G :=
  if h : e i = 1 then
    FiniteIndexNormalSubgroup.ofSubgroup (⊤ : Subgroup G)
  else
    (Group.exists_finiteIndexNormalSubgroup_notMem (e i) h).choose

open scoped Classical in
theorem rfChoice_notMem [Group.ResiduallyFinite G] (e : ℕ → G) (i : ℕ)
    (h : e i ≠ 1) : e i ∉ (rfChoice e i).toSubgroup := by
  unfold rfChoice
  rw [dif_neg h]
  exact (Group.exists_finiteIndexNormalSubgroup_notMem (e i) h).choose_spec

/-- The `i`-th chosen finite-index normal subgroup, as a bare `Subgroup`. -/
noncomputable def rfHsub [Group.ResiduallyFinite G] (e : ℕ → G) (i : ℕ) :
    Subgroup G :=
  (rfChoice e i).toSubgroup

noncomputable instance rfHsub_normal [Group.ResiduallyFinite G]
    (e : ℕ → G) (i : ℕ) : (rfHsub e i).Normal :=
  (rfChoice e i).isNormal'

noncomputable instance rfHsub_finiteIndex [Group.ResiduallyFinite G]
    (e : ℕ → G) (i : ℕ) : (rfHsub e i).FiniteIndex :=
  (rfChoice e i).isFiniteIndex'

/-- The running finite meet `H₀ ⊓ H₁ ⊓ ⋯ ⊓ Hₖ`, i.e. the printed `N_k`. -/
noncomputable def rfN [Group.ResiduallyFinite G] (e : ℕ → G) : ℕ → Subgroup G
  | 0 => rfHsub e 0
  | (k + 1) => rfN e k ⊓ rfHsub e (k + 1)

noncomputable instance rfN_normal [Group.ResiduallyFinite G]
    (e : ℕ → G) : ∀ k, (rfN e k).Normal
  | 0 => rfHsub_normal e 0
  | (k + 1) => by
      haveI := rfN_normal e k
      show (rfN e k ⊓ rfHsub e (k + 1)).Normal
      exact Subgroup.normal_inf_normal (rfN e k) (rfHsub e (k + 1))

noncomputable instance rfN_finiteIndex [Group.ResiduallyFinite G]
    (e : ℕ → G) : ∀ k, (rfN e k).FiniteIndex
  | 0 => rfHsub_finiteIndex e 0
  | (k + 1) => by
      haveI := rfN_finiteIndex e k
      show (rfN e k ⊓ rfHsub e (k + 1)).FiniteIndex
      infer_instance

theorem rfN_succ_le [Group.ResiduallyFinite G] (e : ℕ → G) (k : ℕ) :
    rfN e (k + 1) ≤ rfN e k :=
  inf_le_left

/-- `N₁ ≥ N₂ ≥ ⋯`: the chosen subgroups are antitone in `k`. -/
theorem rfN_antitone [Group.ResiduallyFinite G] (e : ℕ → G) :
    Antitone (rfN e) :=
  antitone_nat_of_succ_le (rfN_succ_le e)

theorem rfN_le_last [Group.ResiduallyFinite G] (e : ℕ → G) : ∀ k, rfN e k ≤ rfHsub e k
  | 0 => le_refl _
  | (_k + 1) => inf_le_right

/-- Since `1` is chosen the correct index, and every nonidentity element is
excluded from its own chosen subgroup and hence from every later member of
the antitone chain, every `g ≠ 1` is eventually excluded from `N_k`. -/
theorem rfN_eventually_notMem [Group.ResiduallyFinite G] (e : ℕ → G)
    (he : Function.Surjective e) (g : G) (hg : g ≠ 1) :
    ∃ m, ∀ k, m ≤ k → g ∉ rfN e k := by
  obtain ⟨i, hi⟩ := he g
  subst hi
  refine ⟨i, fun _k hk hmem => ?_⟩
  exact rfChoice_notMem e i hg (((rfN_antitone e hk).trans (rfN_le_last e i)) hmem)

/-- The printed "trivial intersection" of `N₁ ≥ N₂ ≥ ⋯`. -/
theorem rfN_iInf_eq_bot [Group.ResiduallyFinite G] (e : ℕ → G)
    (he : Function.Surjective e) : ⨅ k, rfN e k = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  by_contra hne
  obtain ⟨m, hm⟩ := rfN_eventually_notMem e he g hne
  exact hm m le_rfl (Subgroup.mem_iInf.mp hg m)

/-- **Sentence `2164704a2652`.**  "Choose finite-index normal subgroups
`N₁ ≥ N₂ ≥ ⋯` with trivial intersection[, and let `λ_k` be the left regular
representation of `G/N_k`, of dimension `d_k`]": every countable residually
finite group has an antitone chain of finite-index normal subgroups with
trivial intersection.  (The regular representations `λ_k` themselves are
constructed below as `rfLambda`, once the finite quotients `G/N_k` are in
hand.) -/
theorem exists_antitone_finiteIndexNormal_trivialIntersection
    (G : Type) [Group G] [Countable G] [Group.ResiduallyFinite G] :
    ∃ N : ℕ → Subgroup G, (∀ k, (N k).Normal) ∧ (∀ k, (N k).FiniteIndex) ∧
      Antitone N ∧ ⨅ k, N k = ⊥ := by
  obtain ⟨e, he⟩ := exists_surjective_nat G
  exact ⟨rfN e, fun k => rfN_normal e k, fun k => rfN_finiteIndex e k,
    rfN_antitone e, rfN_iInf_eq_bot e he⟩

end RfRegularTower

/-! ## The exact left regular representation of a finite group -/

section FiniteGroupRegularRep

variable (Y : FiniteModel) [Group Y]

/-- **`λ_k`, the left regular representation of a finite group, as a unitary
representation.**  This is the object named in sentence `2164704a2652`.
Corrected into a genuine homomorphism by inverting first (`permMatrix` is an
anti-homomorphism, so `q ↦ (leftRegular q)⁻¹.permMatrix ℂ` is a
homomorphism): the mirror of the computation used throughout the repository
(e.g. `NormTraceGap.isNormApproximable_of_finite`) for the regular
representation of a finite group. -/
noncomputable def finiteGroupRegularHom : Y →* Matrix.unitaryGroup Y ℂ where
  toFun q := ⟨((leftRegular q)⁻¹).permMatrix ℂ, permMatrix_mem_unitaryGroup Y _⟩
  map_one' := by
    apply Subtype.ext
    show ((leftRegular (1 : Y))⁻¹).permMatrix ℂ = 1
    simp [leftRegular]
  map_mul' q r := by
    apply Subtype.ext
    show ((leftRegular (q * r))⁻¹).permMatrix ℂ =
      ((leftRegular q)⁻¹).permMatrix ℂ * ((leftRegular r)⁻¹).permMatrix ℂ
    rw [leftRegular_mul, mul_inv_rev, Matrix.permMatrix_mul]

theorem coe_finiteGroupRegularHom (q : Y) :
    (finiteGroupRegularHom Y q : Matrix Y Y ℂ) = ((leftRegular q)⁻¹).permMatrix ℂ :=
  rfl

omit [Group Y] in
/-- Hamming distance is invariant under simultaneously inverting both
arguments (right-translate both sides by the first argument, then use
commutativity of `hammingDistance`). -/
theorem hammingDistance_inv_one_eq (σ : Equiv.Perm Y) :
    hammingDistance Y σ⁻¹ 1 = hammingDistance Y σ 1 := by
  have h := hammingDistance_right_invariant Y σ⁻¹ 1 σ
  rw [inv_mul_cancel, one_mul] at h
  rw [← h]
  exact hammingDistance_comm Y 1 σ

/-- The left regular representation of a nonidentity element has trace `0`:
its permutation is fixed-point-free, by the standard group cancellation
argument, hence its normalized character vanishes. -/
theorem normTrace_finiteGroupRegularHom_of_ne_one [Nonempty Y] (q : Y)
    (hq : q ≠ 1) :
    normTrace Y (finiteGroupRegularHom Y q : Matrix Y Y ℂ) = 0 := by
  classical
  rw [coe_finiteGroupRegularHom, normTrace_permMatrix Y _ Fintype.card_pos]
  have h1 : hammingDistance Y (leftRegular q) 1 = 1 := by
    rw [hammingDistance_eq_support]
    have hsupp : ((1 : Equiv.Perm Y)⁻¹ * leftRegular q).support = Finset.univ := by
      ext x
      simp only [inv_one, one_mul, Equiv.Perm.mem_support, Finset.mem_univ,
        iff_true]
      intro hfix
      apply hq
      have hqx : q * x = x := by simpa [leftRegular] using hfix
      have h2 := congrArg (· * x⁻¹) hqx
      simpa using h2
    rw [hsupp, Finset.card_univ, div_self]
    exact_mod_cast Fintype.card_pos.ne'
  rw [hammingDistance_inv_one_eq Y (leftRegular q), h1]
  norm_num

/-- Two distinct elements have regular representations at operator-norm
distance at least `1`: the two permutation matrices already disagree at the
single entry indexed by `(1, q⁻¹)`. -/
theorem finiteGroupRegularHom_separated [Nonempty Y] {q r : Y} (hqr : q ≠ r) :
    (1 : ℝ) ≤ ‖(finiteGroupRegularHom Y q : Matrix Y Y ℂ) -
      (finiteGroupRegularHom Y r : Matrix Y Y ℂ)‖ := by
  classical
  have hg1 : (leftRegular q)⁻¹ (1 : Y) = q⁻¹ := by simp [leftRegular]
  have hh1 : ¬ (leftRegular r)⁻¹ (1 : Y) = q⁻¹ := by
    have hr1 : (leftRegular r)⁻¹ (1 : Y) = r⁻¹ := by simp [leftRegular]
    rw [hr1]
    exact fun hcon => hqr (inv_injective hcon).symm
  have hGent := permMatrixC_entry Y (leftRegular q)⁻¹ (1 : Y) q⁻¹
  have hHent := permMatrixC_entry Y (leftRegular r)⁻¹ (1 : Y) q⁻¹
  rw [if_pos hg1] at hGent
  rw [if_neg hh1] at hHent
  have hentry : Complex.normSq
      ((((leftRegular q)⁻¹).permMatrix ℂ - ((leftRegular r)⁻¹).permMatrix ℂ)
        (1 : Y) q⁻¹) = 1 := by
    rw [Matrix.sub_apply, hGent, hHent, sub_zero]
    simp
  have hbound := normSq_entry_le_sq_l2_opNorm Y
    (((leftRegular q)⁻¹).permMatrix ℂ - ((leftRegular r)⁻¹).permMatrix ℂ)
    (1 : Y) q⁻¹
  rw [hentry] at hbound
  rw [coe_finiteGroupRegularHom, coe_finiteGroupRegularHom]
  nlinarith [norm_nonneg (((leftRegular q)⁻¹).permMatrix ℂ -
    ((leftRegular r)⁻¹).permMatrix ℂ)]

end FiniteGroupRegularRep

/-! ## `lem:rf-regular`, sentences `11ef4e40cdb1` and `105f4a037a61` -/

section RfRegularRealization

variable {G : Type} [Group G] [Countable G] [Group.ResiduallyFinite G]

omit [Countable G] in
noncomputable instance rfModel_fintype (e : ℕ → G) (n : ℕ) :
    Fintype (G ⧸ rfN e n) :=
  haveI : Finite (G ⧸ rfN e n) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

omit [Countable G] in
noncomputable instance rfModel_decidableEq (e : ℕ → G) (n : ℕ) :
    DecidableEq (G ⧸ rfN e n) :=
  Classical.decEq _

omit [Countable G] in
/-- The finite quotient `G/N_k`, bundled as a `FiniteModel`. -/
@[reducible] noncomputable def rfModel (e : ℕ → G) (n : ℕ) : FiniteModel :=
  ⟨G ⧸ rfN e n, rfModel_fintype e n, rfModel_decidableEq e n⟩

omit [Countable G] in
noncomputable instance rfModel_nonempty (e : ℕ → G) (n : ℕ) :
    Nonempty (rfModel e n) :=
  ⟨(1 : G ⧸ rfN e n)⟩

omit [Countable G] in
/-- The composite `G ↠ G/N_k → U(d_k)`: exactly the printed `λ_k` applied to
the tower produced by `exists_antitone_finiteIndexNormal_trivialIntersection`.
This is an honest group homomorphism, with no asymptotic defect. -/
noncomputable def rfLambda (e : ℕ → G) (n : ℕ) : G →* Matrix.unitaryGroup (rfModel e n) ℂ :=
  (finiteGroupRegularHom (rfModel e n)).comp (QuotientGroup.mk' (rfN e n))

omit [Countable G] in
theorem rfMk_eq_iff (e : ℕ → G) (n : ℕ) (g h : G) :
    QuotientGroup.mk' (rfN e n) g = QuotientGroup.mk' (rfN e n) h ↔
      g⁻¹ * h ∈ rfN e n :=
  QuotientGroup.eq

omit [Countable G] in
theorem rfLambda_apply (e : ℕ → G) (n : ℕ) (g : G) :
    rfLambda e n g = finiteGroupRegularHom (rfModel e n) (QuotientGroup.mk' (rfN e n) g) :=
  rfl

omit [Countable G] in
/-- Packaging the literal tower as a `RegularTraceWeakMFApproximation`: the
"eventually" clauses reduce to `rfN_eventually_notMem`, and the
multiplicative and trace laws are exact because `rfLambda` is a genuine
homomorphism landing in a trace-vanishing regular representation. -/
noncomputable def rfRegularTraceApprox (e : ℕ → G) (he : Function.Surjective e) :
    RegularTraceWeakMFApproximation G where
  separation := 1
  separation_pos := one_pos
  model := rfModel e
  modelNonempty := fun n => Fintype.card_pos
  map := fun n g => rfLambda e n g
  asymptoticallyMultiplicative := fun g h ε hε =>
    ⟨0, fun n _ => by
      have heq : (rfLambda e n (g * h) : Matrix (rfModel e n) (rfModel e n) ℂ) =
          (rfLambda e n g : Matrix (rfModel e n) (rfModel e n) ℂ) *
            (rfLambda e n h : Matrix (rfModel e n) (rfModel e n) ℂ) := by
        simp [map_mul]
      rw [heq, sub_self, norm_zero]
      exact hε.le⟩
  separatedEventually := fun g h hgh => by
    classical
    obtain ⟨m, hm⟩ := rfN_eventually_notMem e he (g⁻¹ * h)
      (fun hcon => hgh (by
        have := congrArg (g * ·) hcon
        simpa using this.symm))
    refine ⟨m, fun n hn => ?_⟩
    have hne : QuotientGroup.mk' (rfN e n) g ≠ QuotientGroup.mk' (rfN e n) h :=
      fun hcon => hm n hn ((rfMk_eq_iff e n g h).mp hcon)
    rw [rfLambda_apply, rfLambda_apply]
    exact finiteGroupRegularHom_separated (rfModel e n) hne
  regularTraceEventually := fun g h hgh => by
    classical
    obtain ⟨m, hm⟩ := rfN_eventually_notMem e he (g * h⁻¹)
      (fun hcon => hgh (mul_inv_eq_one.mp hcon))
    refine ⟨m, fun n hn => ?_⟩
    have hstar : Matrix.conjTranspose
        (rfLambda e n h : Matrix (rfModel e n) (rfModel e n) ℂ) =
        (rfLambda e n h⁻¹ : Matrix (rfModel e n) (rfModel e n) ℂ) := by
      rw [← Matrix.star_eq_conjTranspose, map_inv, ← Unitary.coe_star,
        Unitary.star_eq_inv]
    have hstep : (rfLambda e n g : Matrix (rfModel e n) (rfModel e n) ℂ) *
        Matrix.conjTranspose (rfLambda e n h : Matrix (rfModel e n) (rfModel e n) ℂ) =
        (rfLambda e n (g * h⁻¹) : Matrix (rfModel e n) (rfModel e n) ℂ) := by
      rw [hstar]
      have hmul : rfLambda e n (g * h⁻¹) = rfLambda e n g * rfLambda e n h⁻¹ :=
        map_mul _ _ _
      rw [hmul]
      rfl
    rw [hstep, rfLambda_apply]
    have hne1 : QuotientGroup.mk' (rfN e n) (g * h⁻¹) ≠ 1 :=
      fun hcon => hm n hn (QuotientGroup.eq_one_iff (g * h⁻¹) |>.mp hcon)
    exact normTrace_finiteGroupRegularHom_of_ne_one (rfModel e n)
      (QuotientGroup.mk' (rfN e n) (g * h⁻¹)) hne1

omit [Countable G] in
/-- **Sentence `11ef4e40cdb1`, first half.**  "In the corona `𝒬_d` the map
`ρ(g)=[(λ_k(g))_k]` is a homomorphism." -/
theorem rho_isMonoidHom (e : ℕ → G) (he : Function.Surjective e) (a b : G) :
    RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom (rfRegularTraceApprox e he) (a * b) =
      RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom (rfRegularTraceApprox e he) a *
        RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom (rfRegularTraceApprox e he) b :=
  map_mul _ a b

omit [Countable G] in
/-- **Sentence `11ef4e40cdb1`, second half.**  "`τ([(x_k)_k])=lim_ω
tr_{d_k}(x_k)`, for a free ultrafilter `ω`, is a tracial state with
`τ(ρ(g))=0` for `g≠1`, since `g∉N_k` for all large `k`."  The tracial state
`τ` is `normMatrixCoronaTracialState` (the canonical ultratrace on the
corona, defined once for all norm matrix coronas); its vanishing off the
identity, on this specific `ρ`, is exactly
`cofiniteCStarCoronaHom_regularTrace` applied to the literal tower. -/
theorem tau_vanishes_off_identity (e : ℕ → G) (he : Function.Surjective e)
    (g : G) (hg : g ≠ 1) :
    letI : ∀ n, Nonempty ((rfRegularTraceApprox e he).model n) := fun n =>
      Fintype.card_pos_iff.mp ((rfRegularTraceApprox e he).modelNonempty n)
    normMatrixCoronaTracialState (rfRegularTraceApprox e he).model
        (RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom
            (rfRegularTraceApprox e he) g :
          NormMatrixCStarCorona (fun n => (rfRegularTraceApprox e he).model n)) = 0 :=
  RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom_regularTrace
    (rfRegularTraceApprox e he) g hg

/-- **Sentence `105f4a037a61`.**  "The `C*`-algebra generated by `ρ(G)` and
the unit of the corona is separable and unital, and the triple with `ρ` and
`τ` is the required realization."  Every countable residually finite group
admits a tracial MF realization, via the literal tower built above (this
strengthens `residuallyFinite_isRegularlyRealized`'s hypothesis-free
conclusion by exhibiting the manuscript's specific printed witness). -/
theorem literalTower_isRegularlyRealized (G : Type) [Group G] [Countable G]
    [Group.ResiduallyFinite G] : IsRegularlyRealized G := by
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let M := rfRegularTraceApprox e he
  let hne : ∀ n, Nonempty (M.model n) := fun n =>
    Fintype.card_pos_iff.mp (M.modelNonempty n)
  letI : ∀ n, Nonempty (M.model n) := hne
  let Q := NormMatrixCStarCorona (fun n => M.model n)
  let rho : G →* unitary Q := RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom M
  let tau : TracialState Q := normMatrixCoronaTracialState M.model
  refine ⟨groupGeneratedCStar rho, inferInstance, ⟨?_⟩⟩
  exact generatedRegularRealization
    (normMatrixCorona_hasMFEmbedding_of_positive M.model hne)
    rho tau
    (fun g hg =>
      RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom_regularTrace M g hg)

end RfRegularRealization

/-! ## The setup preceding `eq:hnn`, sentences `d2d6f8c60b94`, `e16e647b7b7d`,
`1127a37962dc` -/

section HNNPermanenceSetup

/-- **Sentence `d2d6f8c60b94`.**  "Let `G` be a countable group, let `S≤G` be
a subgroup, and let `θ:S→G` be an injective homomorphism."  The hypothesis
package feeding `eq:hnn`. -/
structure HNNPermanenceHypotheses where
  G : Type
  [instGroupG : Group G]
  [instCountableG : Countable G]
  S : Subgroup G
  theta : S →* G
  theta_injective : Function.Injective theta

namespace HNNPermanenceHypotheses

attribute [instance] instGroupG instCountableG

variable (H : HNNPermanenceHypotheses)

/-- **Sentence `e16e647b7b7d`.**  "The HNN extension
`R = ⟨G,t ∣ tst⁻¹=θ(s) (s∈S)⟩`" of `eq:hnn`. -/
def R : Type :=
  HNNExtension H.G H.S (MonoidHom.range H.theta)
    (MonoidHom.ofInjective H.theta_injective)

noncomputable instance : Group H.R :=
  inferInstanceAs (Group (HNNExtension H.G H.S (MonoidHom.range H.theta)
    (MonoidHom.ofInjective H.theta_injective)))

/-- **Sentence `1127a37962dc`.**  "\[`R`\] contains `G` by Britton's
lemma." -/
theorem R_contains_G : Function.Injective
    (HNNExtension.of : H.G →* H.R) :=
  hnnExtension_base_injective (MonoidHom.ofInjective H.theta_injective)

end HNNPermanenceHypotheses

end HNNPermanenceSetup

/-! ## `lem:reduced-products`, sentences `9f790b48eb4f` and `cc882ce8c806` -/

section ReducedProducts

/-- **The reduced-products peer lane's cited input.**  Clause 1 of
`lem:reduced-products`: "If every `B_n` is MF, then every separable
`C*`-subalgebra of `∏ₙBₙ/⊕ₙBₙ` is MF."  The ambient reduced product itself
(`PolarLiftingGeneralCStar.CStarProductCorona`, at the cofinite filter) is
already in the repository; its bundled `CStarAlgebra`/`StarModule` instances
(closedness and star-stability of the null-sequence ideal) and the fact that
the closed subalgebra `C` inherits a genuine `NonUnitalCStarAlgebra`
structure are the `reduced-products` lane's own construction, so they are
supplied as data rather than found by instance search.  A consumer takes a
term of this Prop as a hypothesis rather than finding a proof below. -/
def ReducedProductSeparableSubalgebraIsMF
    (B : ℕ → Type) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    [CStarAlgebra (PolarLiftingGeneralCStar.CStarProductCorona B Filter.cofinite)]
    [StarModule ℂ (PolarLiftingGeneralCStar.CStarProductCorona B Filter.cofinite)]
    (C : StarSubalgebra ℂ
      (PolarLiftingGeneralCStar.CStarProductCorona B Filter.cofinite))
    [NonUnitalCStarAlgebra C] : Prop :=
  (∀ n, IsMFAlgebra (B n)) → IsClosed (C : Set (PolarLiftingGeneralCStar.CStarProductCorona B Filter.cofinite)) →
    TopologicalSpace.SeparableSpace C → IsMFAlgebra C

/-- **Sentence `9f790b48eb4f` (attribution only).**  "The first assertion
follows by diagonalization from the matrix-corona characterization of MF
algebras (Blackadar--Kirchberg; see also [Chapter 11]{BrownOzawa}), and
Korchagin uses it in this form [Proposition 6]{Korchagin}."  This is the
lemma's own first clause, quoted here with its attribution, and consumed
from `ReducedProductSeparableSubalgebraIsMF` as a leading hypothesis. -/
theorem reducedProduct_separableSubalgebra_isMF_sentence
    (B : ℕ → Type) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    [CStarAlgebra (PolarLiftingGeneralCStar.CStarProductCorona B Filter.cofinite)]
    [StarModule ℂ (PolarLiftingGeneralCStar.CStarProductCorona B Filter.cofinite)]
    (C : StarSubalgebra ℂ
      (PolarLiftingGeneralCStar.CStarProductCorona B Filter.cofinite))
    [NonUnitalCStarAlgebra C]
    (hWiring : ReducedProductSeparableSubalgebraIsMF B C)
    (hB : ∀ n, IsMFAlgebra (B n)) (hC : IsClosed (C : Set (PolarLiftingGeneralCStar.CStarProductCorona B Filter.cofinite)))
    (hCsep : TopologicalSpace.SeparableSpace C) :
    IsMFAlgebra C :=
  hWiring hB hC hCsep

/-- **Sentence `cc882ce8c806`.**  "The second holds because `M_k` of a norm
matrix corona is the norm matrix corona of the dimension sequence multiplied
by `k`."  Realized by the injective amplification map `matrixCoronaHom`. -/
theorem matrixAmplification_isCoronaOfScaledDimensionSequence
    (k : ℕ) [Nonempty (Fin k)] (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    ∃ phi : CStarMatrix (Fin k) (Fin k)
        (NormMatrixCStarCorona (fun n => X n)) →⋆ₙₐ[ℂ]
        NormMatrixCStarCorona (fun n => AmplifiedBlocks.ampModel k (X n)),
      Function.Injective phi :=
  ⟨MFAlgebraMatrixAmplification.matrixCoronaHom X,
    MFAlgebraMatrixAmplification.matrixCoronaHom_injective X⟩

/-- **`lem:reduced-products`, clause 2, wrapped.**  "Moreover, `M_k(B)` is MF
whenever `B` is."  Aliased directly (no independent type ascription) so that
the local `PartialOrder`-derived `NonUnitalCStarAlgebra (CStarMatrix ...)`
instance used by `isMFAlgebra_cstarMatrix`'s own file is not re-demanded in a
fresh context here. -/
alias lemReducedProducts_matrixAmplification_isMF := isMFAlgebra_cstarMatrix

end ReducedProducts

end

end Sentences
end MFRecognition
end Manuscript
end GroupApproximation
