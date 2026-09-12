import GroupApproximation.Analysis.CStarCPStarTarget
import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Analysis.QuasidiagonalTraceLocal
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite-local NF approximations

This module introduces an NF predicate independently of nuclearity and MF
embeddability.  Its data are the local approximation data suggested by the
name “nuclear finite-dimensional”: completely positive contractions through
a finite-dimensional C⋆-algebra which both recover a prescribed finite set
and are approximately multiplicative there.

The definition is deliberately not an abbreviation for “nuclear and MF”.
Consequently the forward half of the Blackadar--Kirchberg characterization
can be proved without circularity.  An NF algebra is separable and nuclear,
and, in the unital case, its approximately multiplicative matrix models give
a faithful matrix-corona embedding.  The converse requires lifting an MF
corona embedding back to finite-local maps when the source is nuclear.  That
lifting implication is not asserted or assumed here.
-/

namespace GroupApproximation

open CStarExactness
open Filter
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-- Matrix blocks at the scoped operator norm are C-star algebras. -/
local instance matrixBlockCStarAlgebra (Z : Type) [Fintype Z] [DecidableEq Z]
    [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- A finite-local NF approximation to `A` on `F` with tolerance `ε`.

The maps are completely positive contractions.  Their composite recovers
each element of `F` in norm, and the downward map is approximately
multiplicative on every ordered pair from `F`. -/
def HasLocalNFApproximation (A : Type u) [NonUnitalCStarAlgebra A]
    (F : Finset A) (ε : ℝ) : Prop :=
  ∃ (Y : FiniteModel) (hY : Nonempty Y),
    letI : Nonempty Y := hY
    ∃ (down : A →ₗ[ℂ] Matrix Y Y ℂ) (up : Matrix Y Y ℂ →ₗ[ℂ] A),
    IsCompletelyPositive down ∧
      IsCompletelyPositive up ∧
      (∀ a : A, ‖down a‖ ≤ ‖a‖) ∧
      (∀ d : Matrix Y Y ℂ, ‖up d‖ ≤ ‖d‖) ∧
      (∀ a ∈ F, ‖up (down a) - a‖ ≤ ε) ∧
      ∀ a ∈ F, ∀ b ∈ F, ‖down (a * b) - down a * down b‖ ≤ ε

/-- A C⋆-algebra is **NF in the finite-local CPC sense** when it is separable
and admits local NF approximations on every finite set and at every positive
tolerance.

Separability is included because the manuscript's Blackadar--Kirchberg
sentence concerns separable NF algebras and because sequential matrix-corona
models require a countable diagonalization. -/
def IsNFAlgebra (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  TopologicalSpace.SeparableSpace A ∧
    ∀ (F : Finset A) (ε : ℝ), 0 < ε → HasLocalNFApproximation A F ε

/-- The finite-local NF predicate contains separability as genuine data. -/
theorem IsNFAlgebra.separable {A : Type u} [NonUnitalCStarAlgebra A]
    (hA : IsNFAlgebra A) : TopologicalSpace.SeparableSpace A :=
  hA.1

/-- An NF algebra supplies a finite-dimensional CPC approximation on every
finite set and at every positive tolerance. -/
theorem IsNFAlgebra.localApproximation
    {A : Type u} [NonUnitalCStarAlgebra A] (hA : IsNFAlgebra A)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    HasLocalNFApproximation A F ε :=
  hA.2 F ε hε

/-- The recovery half of a local NF approximation, exposed without the
approximately multiplicative clause. -/
theorem HasLocalNFApproximation.recovery
    {A : Type u} [NonUnitalCStarAlgebra A] {F : Finset A} {ε : ℝ}
    (h : HasLocalNFApproximation A F ε) :
    ∃ (Y : FiniteModel) (hY : Nonempty Y),
      letI : Nonempty Y := hY
      ∃ (down : A →ₗ[ℂ] Matrix Y Y ℂ) (up : Matrix Y Y ℂ →ₗ[ℂ] A),
      IsCompletelyPositive down ∧
        IsCompletelyPositive up ∧
        (∀ a : A, ‖down a‖ ≤ ‖a‖) ∧
        (∀ d : Matrix Y Y ℂ, ‖up d‖ ≤ ‖d‖) ∧
        ∀ a ∈ F, ‖up (down a) - a‖ ≤ ε := by
  obtain ⟨Y, hY, down, up, hdownCP, hupCP, hdownContractive,
    hupContractive, hrecover, -⟩ := h
  exact ⟨Y, hY, down, up, hdownCP, hupCP, hdownContractive,
    hupContractive, hrecover⟩

/-- The approximately multiplicative half of a local NF approximation,
retaining the same CPC maps and recovery estimate. -/
theorem HasLocalNFApproximation.approximatelyMultiplicative
    {A : Type u} [NonUnitalCStarAlgebra A] {F : Finset A} {ε : ℝ}
    (h : HasLocalNFApproximation A F ε) :
    ∃ (Y : FiniteModel) (hY : Nonempty Y),
      letI : Nonempty Y := hY
      ∃ (down : A →ₗ[ℂ] Matrix Y Y ℂ) (up : Matrix Y Y ℂ →ₗ[ℂ] A),
      IsCompletelyPositive down ∧
        IsCompletelyPositive up ∧
        (∀ a : A, ‖down a‖ ≤ ‖a‖) ∧
        (∀ d : Matrix Y Y ℂ, ‖up d‖ ≤ ‖d‖) ∧
        (∀ a ∈ F, ‖up (down a) - a‖ ≤ ε) ∧
        ∀ a ∈ F, ∀ b ∈ F,
          ‖down (a * b) - down a * down b‖ ≤ ε :=
  h

/-- Every finite-local NF algebra is nuclear.  The proof uses the same CPC
factorization and simply forgets its approximate-multiplicativity estimate. -/
theorem IsNFAlgebra.isNuclearCStarAlgebra
    {A : Type u} [NonUnitalCStarAlgebra A] (hA : IsNFAlgebra A) :
    IsNuclearCStarAlgebra A := by
  intro F ε hε
  obtain ⟨D, _hD, down, up, hdownCP, hupCP, hdownContractive,
    hupContractive, hrecover, -⟩ := hA.localApproximation F ε hε
  letI : Nonempty D := _hD
  let block : FinDimCStarAlgebra := { carrier := Matrix D D ℂ }
  exact ⟨block, down, up, hdownCP, hupCP, hdownContractive,
    hupContractive, fun a ha ↦ by simpa using hrecover a ha⟩

/-- The directly established half of the NF profile: separability and
nuclearity, with no MF or lifting theorem assumed. -/
theorem IsNFAlgebra.separable_and_nuclear
    {A : Type u} [NonUnitalCStarAlgebra A] (hA : IsNFAlgebra A) :
    TopologicalSpace.SeparableSpace A ∧ IsNuclearCStarAlgebra A :=
  ⟨hA.separable, hA.isNuclearCStarAlgebra⟩

/-- The finite-local NF predicate is inhabited: the one-dimensional matrix
algebra has exact identity approximations through itself. -/
theorem isNFAlgebra_matrixFinOne :
    IsNFAlgebra (Matrix (Fin 1) (Fin 1) ℂ) := by
  refine ⟨inferInstance, ?_⟩
  intro F ε hε
  let Y : FiniteModel := ⟨Fin 1, inferInstance, inferInstance⟩
  have hY : Nonempty Y := ⟨0⟩
  refine ⟨Y, hY, ?_⟩
  letI : Nonempty Y := hY
  refine ⟨LinearMap.id, LinearMap.id,
    CStarExactness.isCompletelyPositive_id,
    CStarExactness.isCompletelyPositive_id, ?_, ?_, ?_, ?_⟩
  · intro a
    exact le_rfl
  · intro d
    exact le_rfl
  · intro a _ha
    simpa only [LinearMap.id_apply, sub_self, norm_zero] using hε.le
  · intro a _ha b _hb
    simpa only [LinearMap.id_apply, sub_self, norm_zero] using hε.le

/-! ## From finite local approximations to a matrix sequence -/

/-- Sequential NF data obtained by diagonalizing the finite-local predicate.
The downward maps are CPC matrix models, their multiplicative defects vanish,
and the CPC factorizations recover every element of the source in norm. -/
structure NFSequenceModel (A : Type u) [NonUnitalCStarAlgebra A]
    (space : ℕ → FiniteModel) [∀ n, Nonempty (space n)] where
  down : ∀ n, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  up : ∀ n, Matrix (space n) (space n) ℂ →ₗ[ℂ] A
  downCompletelyPositive : ∀ n, IsCompletelyPositive (down n)
  upCompletelyPositive : ∀ n, IsCompletelyPositive (up n)
  downContractive : ∀ n (a : A), ‖down n a‖ ≤ ‖a‖
  upContractive : ∀ n (d : Matrix (space n) (space n) ℂ),
    ‖up n d‖ ≤ ‖d‖
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖down n (a * b) - down n a * down n b‖) atTop (nhds 0)
  tendsto_recovery : ∀ a : A,
    Tendsto (fun n ↦ ‖up n (down n a) - a‖) atTop (nhds 0)

/-- Moving the recovery estimate from a nearby point to the desired point
costs two contraction estimates. -/
theorem norm_recovery_le {A : Type u} [NonUnitalCStarAlgebra A]
    {Y : FiniteModel} (down : A →ₗ[ℂ] Matrix Y Y ℂ)
    (up : Matrix Y Y ℂ →ₗ[ℂ] A)
    (hdown : ∀ a : A, ‖down a‖ ≤ ‖a‖)
    (hup : ∀ d : Matrix Y Y ℂ, ‖up d‖ ≤ ‖d‖)
    (x p : A) {η : ℝ} (hp : ‖up (down p) - p‖ ≤ η) :
    ‖up (down x) - x‖ ≤ 2 * ‖x - p‖ + η := by
  have he : up (down x) - x =
      (up (down x) - up (down p)) + (up (down p) - p) + (p - x) := by
    abel
  have hxp : ‖up (down x) - up (down p)‖ ≤ ‖x - p‖ := by
    rw [← map_sub, ← map_sub]
    exact (hup _).trans (hdown _)
  rw [he]
  have hsum := norm_add_le
    ((up (down x) - up (down p)) + (up (down p) - p)) (p - x)
  have hfirst := norm_add_le (up (down x) - up (down p)) (up (down p) - p)
  rw [norm_sub_rev p x] at hsum
  linarith

/-- On a separable algebra, finite-local NF approximations diagonalize to a
single sequence of positive-dimensional matrix models. -/
theorem IsNFAlgebra.exists_sequenceModel
    {A : Type u} [CStarAlgebra A] (hA : IsNFAlgebra A) :
    ∃ (space : ℕ → FiniteModel) (hne : ∀ n, Nonempty (space n)),
      letI : ∀ n, Nonempty (space n) := hne
      Nonempty (NFSequenceModel A space) := by
  classical
  haveI := hA.separable
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq A
  have hchoice : ∀ n : ℕ,
      ∃ (Y : FiniteModel) (hY : Nonempty Y),
        letI : Nonempty Y := hY
        ∃ (down : A →ₗ[ℂ] Matrix Y Y ℂ) (up : Matrix Y Y ℂ →ₗ[ℂ] A),
        IsCompletelyPositive down ∧ IsCompletelyPositive up ∧
          (∀ a : A, ‖down a‖ ≤ ‖a‖) ∧
          (∀ d : Matrix Y Y ℂ, ‖up d‖ ≤ ‖d‖) ∧
          (∀ i ≤ n, ‖up (down (u i)) - u i‖ ≤ 1 / ((n : ℝ) + 1)) ∧
          ∀ i ≤ n, ∀ j ≤ n,
            ‖down (u i * u j) - down (u i) * down (u j)‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨Y, hY, down, up, hdownCP, hupCP, hdown, hup, hrecover, hmul⟩ :=
      hA.localApproximation ((Finset.range (n + 1)).image u)
        (1 / ((n : ℝ) + 1)) (by positivity)
    have hmem : ∀ i ≤ n, u i ∈ (Finset.range (n + 1)).image u := fun i hi ↦
      Finset.mem_image_of_mem u (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact ⟨Y, hY, down, up, hdownCP, hupCP, hdown, hup,
      fun i hi ↦ hrecover (u i) (hmem i hi),
      fun i hi j hj ↦ hmul (u i) (hmem i hi) (u j) (hmem j hj)⟩
  choose space hne down up hdownCP hupCP hdown hup hrecover hmul using hchoice
  letI : ∀ n, Nonempty (space n) := hne
  have hdiv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    fun ε hε ↦ TracialUltraproduct.eventually_lt_of_tendsto_zero
      tendsto_one_div_add_atTop_nhds_zero_nat hε
  refine ⟨space, hne, ⟨{
    down := down
    up := up
    downCompletelyPositive := hdownCP
    upCompletelyPositive := hupCP
    downContractive := hdown
    upContractive := hup
    tendsto_mul := ?_
    tendsto_recovery := ?_
  }⟩⟩
  · intro a b
    refine TracialUltraproduct.tendsto_zero_of_forall_eventually_lt
      (fun n ↦ norm_nonneg _) ?_
    intro ε hε
    obtain ⟨δ, hδ0, hδ1, hδK⟩ := Quasidiagonal.exists_small_scale
      (2 * ‖a‖ + 2 * ‖b‖ + 2) (ε / 2) (by positivity) (by linarith)
    obtain ⟨i, hi⟩ := hu.exists_dist_lt a hδ0
    obtain ⟨j, hj⟩ := hu.exists_dist_lt b hδ0
    rw [dist_eq_norm] at hi hj
    filter_upwards [hdiv (ε / 2) (by linarith), Filter.eventually_ge_atTop i,
      Filter.eventually_ge_atTop j] with n hn hni hnj
    have hai : ‖a - u i‖ ≤ δ := hi.le
    have hbj : ‖b - u j‖ ≤ δ := hj.le
    have hia : ‖u i - a‖ ≤ δ := by rw [norm_sub_rev]; exact hi.le
    have hjb : ‖u j - b‖ ≤ δ := by rw [norm_sub_rev]; exact hj.le
    have hui : ‖u i‖ ≤ ‖a‖ + 1 :=
      (Quasidiagonal.norm_le_of_norm_sub_le hia).trans (by linarith)
    have huj : ‖u j‖ ≤ ‖b‖ + 1 :=
      (Quasidiagonal.norm_le_of_norm_sub_le hjb).trans (by linarith)
    have hkey := Quasidiagonal.norm_mul_defect_le (down n) (hdown n)
      a b (u i) (u j) (hmul n i hni j hnj)
    have hprod : ‖a * b - u i * u j‖ ≤ ‖a‖ * δ + δ * (‖b‖ + 1) := by
      refine (Quasidiagonal.norm_mul_sub_mul_le a b (u i) (u j)).trans ?_
      exact add_le_add (mul_le_mul_of_nonneg_left hbj (norm_nonneg a))
        (mul_le_mul hai huj (norm_nonneg _) hδ0.le)
    have hlast : ‖u i‖ * ‖u j - b‖ + ‖u i - a‖ * ‖b‖
        ≤ (‖a‖ + 1) * δ + δ * ‖b‖ :=
      add_le_add (mul_le_mul hui hjb (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right hia (norm_nonneg b))
    linarith [hkey, hprod, hlast, hδK, hn]
  · intro a
    refine TracialUltraproduct.tendsto_zero_of_forall_eventually_lt
      (fun n ↦ norm_nonneg _) ?_
    intro ε hε
    obtain ⟨i, hi⟩ := hu.exists_dist_lt a (show (0 : ℝ) < ε / 6 by linarith)
    rw [dist_eq_norm] at hi
    filter_upwards [hdiv (ε / 3) (by linarith), Filter.eventually_ge_atTop i]
      with n hn hni
    have hkey := norm_recovery_le (down n) (up n) (hdown n) (hup n)
      a (u i) (hrecover n i hni)
    linarith

/-! ## The faithful homomorphism into the matrix corona -/

namespace NFSequenceModel

variable {A : Type u} [CStarAlgebra A] {space : ℕ → FiniteModel}
  [∀ n, Nonempty (space n)]

/-- The matrix values of a fixed element form a bounded sequence because all
downward maps are contractions. -/
def seq (M : NFSequenceModel A space) (a : A) :
    BoundedMatrixSequence (fun n ↦ space n) :=
  ⟨fun n ↦ M.down n a, memℓp_infty_iff.mpr ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    exact M.downContractive n a⟩⟩

@[simp] theorem seq_apply (M : NFSequenceModel A space) (a : A) (n : ℕ) :
    M.seq a n = M.down n a := rfl

theorem seq_zero (M : NFSequenceModel A space) : M.seq 0 = 0 := by
  refine lp.ext (funext fun n ↦ ?_)
  simp

theorem seq_add (M : NFSequenceModel A space) (a b : A) :
    M.seq (a + b) = M.seq a + M.seq b := by
  refine lp.ext (funext fun n ↦ ?_)
  simp

theorem seq_smul (M : NFSequenceModel A space) (c : ℂ) (a : A) :
    M.seq (c • a) = c • M.seq a := by
  refine lp.ext (funext fun n ↦ ?_)
  simp

theorem seq_star (M : NFSequenceModel A space) (a : A) :
    M.seq (star a) = star (M.seq a) := by
  refine lp.ext (funext fun n ↦ ?_)
  change M.down n (star a) = star (M.down n a)
  exact OrderZero.map_star_of_cp (M.downCompletelyPositive n) a

/-- The asymptotically multiplicative CPC matrix models induce an exact
nonunital star homomorphism into the norm-matrix corona. -/
def coronaHom (M : NFSequenceModel A space) :
    A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ space n) where
  toFun a := normMatrixCStarCoronaQuotient (fun n ↦ space n) (M.seq a)
  map_smul' c a := by
    rw [M.seq_smul, map_smul]
    rfl
  map_zero' := by
    rw [M.seq_zero, map_zero]
  map_add' a b := by
    rw [M.seq_add, map_add]
  map_mul' a b := by
    have hzero : normMatrixCStarCoronaMk (fun n ↦ space n)
        (M.seq (a * b) - M.seq a * M.seq b) = 0 := by
      rw [normMatrixCStarCoronaMk_eq_zero_iff, IsNullMatrixSequence,
        Nat.cofinite_eq_atTop]
      exact (M.tendsto_mul a b).congr fun n ↦ by
        change
          ‖M.down n (a * b) - M.down n a * M.down n b‖ =
            ‖M.down n (a * b) - M.down n a * M.down n b‖
        rfl
    rw [map_sub, map_mul, sub_eq_zero] at hzero
    exact hzero
  map_star' a := by
    rw [M.seq_star, map_star]

@[simp] theorem coronaHom_apply (M : NFSequenceModel A space) (a : A) :
    M.coronaHom a = normMatrixCStarCoronaMk (fun n ↦ space n) (M.seq a) := rfl

/-- Recovery through contractive upward maps forces the corona homomorphism
to be faithful. -/
theorem coronaHom_injective (M : NFSequenceModel A space) :
    Function.Injective M.coronaHom := by
  intro a b hab
  have hkernel : M.coronaHom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hdown : Tendsto (fun n ↦ ‖M.down n (a - b)‖) atTop (nhds 0) := by
    rw [coronaHom_apply, normMatrixCStarCoronaMk_eq_zero_iff,
      IsNullMatrixSequence, Nat.cofinite_eq_atTop] at hkernel
    exact hkernel.congr fun n ↦ by rw [seq_apply]
  have hlimit : Tendsto
      (fun n ↦ ‖M.up n (M.down n (a - b)) - (a - b)‖ + ‖M.down n (a - b)‖)
      atTop (nhds 0) := by
    simpa only [zero_add] using (M.tendsto_recovery (a - b)).add hdown
  have hbound : ∀ n,
      ‖a - b‖ ≤ ‖M.up n (M.down n (a - b)) - (a - b)‖ + ‖M.down n (a - b)‖ := by
    intro n
    have he : a - b = -(M.up n (M.down n (a - b)) - (a - b))
        + M.up n (M.down n (a - b)) := by
      abel
    calc
      ‖a - b‖ = ‖-(M.up n (M.down n (a - b)) - (a - b))
          + M.up n (M.down n (a - b))‖ := congrArg norm he
      _ ≤ ‖-(M.up n (M.down n (a - b)) - (a - b))‖
          + ‖M.up n (M.down n (a - b))‖ := norm_add_le _ _
      _ = ‖M.up n (M.down n (a - b)) - (a - b)‖
          + ‖M.up n (M.down n (a - b))‖ := by rw [norm_neg]
      _ ≤ ‖M.up n (M.down n (a - b)) - (a - b)‖
          + ‖M.down n (a - b)‖ :=
        add_le_add (le_refl _) (M.upContractive n (M.down n (a - b)))
  have hnorm : ‖a - b‖ = 0 :=
    le_antisymm
      (le_of_tendsto_of_tendsto' tendsto_const_nhds hlimit hbound)
      (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end NFSequenceModel

/-- Every unital C-star algebra satisfying the independent finite-local NF
predicate is MF.  The proof constructs the faithful corona embedding and then
uses dimension normalization; it does not unfold MF into the definition of NF. -/
theorem IsNFAlgebra.isMFAlgebra
    {A : Type u} [CStarAlgebra A] (hA : IsNFAlgebra A) : IsMFAlgebra A := by
  obtain ⟨space, hne, ⟨M⟩⟩ := hA.exists_sequenceModel
  letI : ∀ n, Nonempty (space n) := hne
  have hunrestricted : MFAlgebraDimension.HasUnrestrictedMFEmbedding A :=
    ⟨space, hne, fun n ↦ Fintype.card_pos_iff.mpr (hne n),
      M.coronaHom, M.coronaHom_injective⟩
  exact ⟨hA.separable, (MFAlgebraDimension.hasMFEmbedding_iff A).mpr hunrestricted⟩

/-- The unconditional direct half of the Blackadar--Kirchberg equivalence for
the finite-local NF predicate. -/
theorem IsNFAlgebra.separable_nuclear_and_mf
    {A : Type u} [CStarAlgebra A] (hA : IsNFAlgebra A) :
    TopologicalSpace.SeparableSpace A ∧
      IsNuclearCStarAlgebra A ∧ IsMFAlgebra A :=
  ⟨hA.separable, hA.isNuclearCStarAlgebra, hA.isMFAlgebra⟩

/-- Proposition-level packaging of the independently defined NF-to-MF
construction. -/
def FiniteLocalNFImpliesMF : Prop :=
  ∀ (A : Type u) [CStarAlgebra A], IsNFAlgebra A → IsMFAlgebra A

theorem finiteLocalNFImpliesMF : FiniteLocalNFImpliesMF := by
  intro A _ hA
  exact hA.isMFAlgebra

/-- The unconditional forward half of the Blackadar--Kirchberg
characterization, packaged with every type and structure binder inside the
proposition. -/
def FiniteLocalNFImpliesSeparableAndNuclear : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A], IsNFAlgebra A →
    TopologicalSpace.SeparableSpace A ∧ IsNuclearCStarAlgebra A

theorem finiteLocalNFImpliesSeparableAndNuclear :
    FiniteLocalNFImpliesSeparableAndNuclear := by
  intro A _ hA
  exact hA.separable_and_nuclear

end
end GroupApproximation

open GroupApproximation

#audit_axioms IsNFAlgebra.separable
#audit_axioms IsNFAlgebra.localApproximation
#audit_axioms HasLocalNFApproximation.recovery
#audit_axioms HasLocalNFApproximation.approximatelyMultiplicative
#audit_axioms IsNFAlgebra.isNuclearCStarAlgebra
#audit_axioms IsNFAlgebra.separable_and_nuclear
#audit_closed_axioms isNFAlgebra_matrixFinOne
#audit_axioms IsNFAlgebra.exists_sequenceModel
#audit_axioms NFSequenceModel.coronaHom_injective
#audit_axioms IsNFAlgebra.isMFAlgebra
#audit_axioms IsNFAlgebra.separable_nuclear_and_mf
#audit_closed_axioms finiteLocalNFImpliesMF
#audit_closed_axioms finiteLocalNFImpliesSeparableAndNuclear
