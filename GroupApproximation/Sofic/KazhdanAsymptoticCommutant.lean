import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Sofic.MarkedCompressionRootCapture

/-!
# Kazhdan transport of asymptotic commutants

This is the sequence-valued form of the compressor argument.  A one-sided
compressor of a Kazhdan image preserves its entire normalized
Hilbert--Schmidt asymptotic commutant in every operator-norm almost
representation.  No distinguished lamp, endomorphism, torsion element, or
marked word occurs in the statement.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

open Matrix KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator

universe u

/-! The manuscript's transport theorem quantifies over an arbitrary ambient
group, so the ambient group is taken in an arbitrary universe here.  Nothing in
the analytic chain constrains it: `OpAlmostRepresentation`,
`KazhdanCompressionCore`, `KazhdanCompressorCorner` and
`MarkedCompressionRootCapture` are all already stated for `E : Type u`.  The
Kazhdan source `Γ` stays in `Type 0` because `KazhdanCompressionCore` spells
property `(T)` as `HasKazhdanPropertyT.{0, 0}`, whose group argument is pinned
to the smallest universe by that notation. -/
variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-- Squared normalized Hilbert--Schmidt convergence to zero. -/
def HSSqVanishing (B : OpAlmostRepresentation E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, hsNormSq (B.model n) (x n) ≤ ε

theorem HSSqVanishing.congr {B : OpAlmostRepresentation E}
    {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x) (hxy : ∀ n, x n = y n) :
    HSSqVanishing B y := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  exact ⟨N, fun n hn ↦ by rw [← hxy n]; exact hN n hn⟩

theorem HSSqVanishing.neg {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x) : HSSqVanishing B (fun n ↦ -x n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnorm : hsNormSq (B.model n) (-x n) = hsNormSq (B.model n) (x n) := by
    rw [show -x n = (-1 : ℂ) • x n by simp, hsNormSq_smul]
    norm_num
  rw [hnorm]
  exact hN n hn

/-- Reversing a difference preserves squared Hilbert--Schmidt nullity. -/
theorem HSSqVanishing.sub_symm {B : OpAlmostRepresentation E}
    {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hxy : HSSqVanishing B (fun n ↦ x n - y n)) :
    HSSqVanishing B (fun n ↦ y n - x n) :=
  hxy.neg.congr fun n ↦ by abel

theorem HSSqVanishing.add {B : OpAlmostRepresentation E}
    {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x) (hy : HSSqVanishing B y) :
    HSSqVanishing B (fun n ↦ x n + y n) := by
  intro ε hε
  obtain ⟨Nx, hNx⟩ := hx (ε / 4) (by linarith)
  obtain ⟨Ny, hNy⟩ := hy (ε / 4) (by linarith)
  refine ⟨max Nx Ny, fun n hn ↦ ?_⟩
  exact (hsNormSq_add_le (B.model n) (x n) (y n)).trans (by
    have hx' := hNx n ((le_max_left _ _).trans hn)
    have hy' := hNy n ((le_max_right _ _).trans hn)
    linarith)

theorem HSSqVanishing.smul {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x) (c : ℂ) :
    HSSqVanishing B (fun n ↦ c • x n) := by
  intro ε hε
  have hden : 0 < Complex.normSq c + 1 := by
    nlinarith [Complex.normSq_nonneg c]
  obtain ⟨N, hN⟩ := hx (ε / (Complex.normSq c + 1)) (div_pos hε hden)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [hsNormSq_smul]
  calc
    Complex.normSq c * hsNormSq (B.model n) (x n) ≤
        Complex.normSq c * (ε / (Complex.normSq c + 1)) :=
      mul_le_mul_of_nonneg_left (hN n hn) (Complex.normSq_nonneg c)
    _ ≤ ε := by
      calc
        Complex.normSq c * (ε / (Complex.normSq c + 1)) =
            ε * (Complex.normSq c / (Complex.normSq c + 1)) := by ring
        _ ≤ ε := by
          have hratio : Complex.normSq c / (Complex.normSq c + 1) ≤ 1 :=
            (div_le_one hden).2 (by linarith [Complex.normSq_nonneg c])
          simpa using mul_le_mul_of_nonneg_left hratio hε.le

theorem HSSqVanishing.finset_sum {B : OpAlmostRepresentation E}
    {I : Type} (s : Finset I)
    (x : I → ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : ∀ i ∈ s, HSSqVanishing B (x i)) :
    HSSqVanishing B (fun n ↦ ∑ i ∈ s, x i n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ε hε
      exact ⟨0, fun n _ ↦ by simp [hsNormSq, hε.le]⟩
  | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using
        (hx i (Finset.mem_insert_self i s)).add
          (ih fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))

theorem HSSqVanishing.unitary_conjugate
    {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ) :
    HSSqVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [hsNormSq_mul_right _ (conjTranspose_mem_unitaryGroup (u n).2),
    hsNormSq_mul_left _ (u n).2 (B.modelNonempty n)]
  exact hN n hn

/-- Operator-norm null sequences are normalized-Hilbert--Schmidt null. -/
theorem HSSqVanishing.of_opNormVanishing
    {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : OpNormVanishing B x) : HSSqVanishing B x := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hx (Real.sqrt epsilon) (Real.sqrt_pos.2 hepsilon)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hdom : hsNormSq (B.model n) (x n) ≤ ‖x n‖ ^ 2 := by
    simpa [hsNormSq, hsDistSq] using
      (hsDistSq_le_sq_l2_opNorm (B.model n) (x n) 0)
  calc
    hsNormSq (B.model n) (x n) ≤ ‖x n‖ ^ 2 := hdom
    _ ≤ (Real.sqrt epsilon) ^ 2 := by
      nlinarith [norm_nonneg (x n), Real.sqrt_nonneg epsilon, hN n hn]
    _ = epsilon := Real.sq_sqrt hepsilon.le

/-- A matrix sequence asymptotically centralizes the image of a homomorphism. -/
def IsAsymptoticCommutantOf (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∀ γ : Γ, HSSqVanishing B (fun n ↦
    x n - (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
      x n * (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)

/-- A bounded matrix sequence asymptotically centralizes the Kazhdan image. -/
abbrev IsAsymptoticCommutant (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Γ E) := IsAsymptoticCommutantOf B C.iota

/-- Uniform operator-norm boundedness of a matrix sequence. -/
def IsUniformlyBounded (B : OpAlmostRepresentation E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M

/-- Exact unitary conjugation preserves uniform boundedness. -/
theorem IsUniformlyBounded.unitary_conjugate
    {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsUniformlyBounded B x)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ) :
    IsUniformlyBounded B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  obtain ⟨M, hM, hMx⟩ := hx
  refine ⟨M, hM, fun n ↦ ?_⟩
  change ‖(u n : Matrix (B.model n) (B.model n) ℂ) * x n *
    (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ ≤ M
  rw [CStarRing.norm_mul_mem_unitary _
      (conjTranspose_mem_unitaryGroup (u n).2),
    CStarRing.norm_mem_unitary_mul _ (u n).2]
  exact hMx n

/-- Hilbert--Schmidt-equivalent bounded sequences have the same asymptotic
commutation relations. -/
theorem IsAsymptoticCommutant.congr_hs
    {B : OpAlmostRepresentation E} {iota : Γ →* E}
    {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsAsymptoticCommutantOf B iota x)
    (hxy : HSSqVanishing B (fun n ↦ x n - y n)) :
    IsAsymptoticCommutantOf B iota y := by
  intro gamma
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ :=
    fun n ↦ B.map n (iota gamma)
  have hconj := hxy.unitary_conjugate u
  have hsum := ((hx gamma).add hxy.neg).add hconj
  exact hsum.congr fun n ↦ by
    have hu : (u n : Matrix (B.model n) (B.model n) ℂ) *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 :=
      Unitary.mul_star_self_of_mem (u n).2
    simp only [u]
    noncomm_ring [hu]

/-- Operator-norm nullity is preserved by conjugate transpose. -/
theorem OpNormVanishing.conjTranspose
    {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : OpNormVanishing B x) :
    OpNormVanishing B (fun n ↦ (x n)ᴴ) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hx epsilon hepsilon
  refine ⟨N, fun n hn ↦ ?_⟩
  change ‖(x n)ᴴ‖ ≤ epsilon
  rw [← Matrix.star_eq_conjTranspose, norm_star]
  exact hN n hn

/-- Conjugating a uniformly bounded sequence by operator-norm-equivalent
unitaries changes it by a Hilbert--Schmidt-null sequence. -/
theorem conjugation_hsSqVanishing_of_opNormVanishing
    {B : OpAlmostRepresentation E}
    (u v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsUniformlyBounded B x)
    (huv : OpNormVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) - v n)) :
    HSSqVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
          (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        (v n : Matrix (B.model n) (B.model n) ℂ) * x n *
          (v n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  apply HSSqVanishing.of_opNormVanishing
  obtain ⟨M, hM, hMx⟩ := hbound
  intro epsilon hepsilon
  have hden : 0 < 2 * (M + 1) := by positivity
  obtain ⟨N, hN⟩ := huv (epsilon / (2 * (M + 1))) (div_pos hepsilon hden)
  refine ⟨N, fun n hn ↦ ?_⟩
  let U : Matrix (B.model n) (B.model n) ℂ := u n
  let V : Matrix (B.model n) (B.model n) ℂ := v n
  let X : Matrix (B.model n) (B.model n) ℂ := x n
  have hsplit : U * X * Uᴴ - V * X * Vᴴ =
      (U - V) * X * Uᴴ + V * X * (U - V)ᴴ := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  change ‖U * X * Uᴴ - V * X * Vᴴ‖ ≤ epsilon
  rw [hsplit]
  have hleft : ‖(U - V) * X * Uᴴ‖ ≤ ‖U - V‖ * ‖X‖ := by
    calc
      ‖(U - V) * X * Uᴴ‖ = ‖(U - V) * X‖ :=
        CStarRing.norm_mul_mem_unitary _
          (conjTranspose_mem_unitaryGroup (u n).2)
      _ ≤ ‖U - V‖ * ‖X‖ := Matrix.l2_opNorm_mul _ _
  have hright : ‖V * X * (U - V)ᴴ‖ ≤ ‖X‖ * ‖U - V‖ := by
    calc
      ‖V * X * (U - V)ᴴ‖ ≤ ‖V * X‖ * ‖(U - V)ᴴ‖ :=
        Matrix.l2_opNorm_mul _ _
      _ = ‖X‖ * ‖U - V‖ := by
        rw [CStarRing.norm_mem_unitary_mul _ (v n).2,
          ← Matrix.star_eq_conjTranspose, norm_star]
  calc
    ‖(U - V) * X * Uᴴ + V * X * (U - V)ᴴ‖ ≤
        ‖(U - V) * X * Uᴴ‖ + ‖V * X * (U - V)ᴴ‖ := norm_add_le _ _
    _ ≤ ‖U - V‖ * ‖X‖ + ‖X‖ * ‖U - V‖ := add_le_add hleft hright
    _ ≤ 2 * M * (epsilon / (2 * (M + 1))) := by
      have hUV : ‖U - V‖ ≤ epsilon / (2 * (M + 1)) := by
        simpa [U, V] using hN n hn
      have hX : ‖X‖ ≤ M := by simpa [X] using hMx n
      nlinarith [norm_nonneg (U - V), norm_nonneg X]
    _ = epsilon * (M / (M + 1)) := by field_simp
    _ ≤ epsilon := by
      have hM1 : 0 < M + 1 := by linarith
      have hratio : M / (M + 1) ≤ 1 := (div_le_one hM1).2 (by linarith)
      simpa using mul_le_mul_of_nonneg_left hratio hepsilon.le

/-- Coordinate adjoint action of a group element. -/
def adjointSequence (B : OpAlmostRepresentation E) (g : E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) := fun n ↦
  (B.map n g : Matrix (B.model n) (B.model n) ℂ) * x n *
    (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ

/-- Coordinate inverse adjoint action of a group element. -/
def coadjointSequence (B : OpAlmostRepresentation E) (g : E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) := fun n ↦
  (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n * B.map n g

theorem IsUniformlyBounded.adjointSequence
    {B : OpAlmostRepresentation E} {g : E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsUniformlyBounded B x) : IsUniformlyBounded B (adjointSequence B g x) :=
  hx.unitary_conjugate (fun n ↦ B.map n g)

theorem IsUniformlyBounded.coadjointSequence
    {B : OpAlmostRepresentation E} {g : E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsUniformlyBounded B x) : IsUniformlyBounded B (coadjointSequence B g x) := by
  obtain ⟨M, hM, hMx⟩ := hx
  refine ⟨M, hM, fun n ↦ ?_⟩
  change ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
    (B.map n g : Matrix (B.model n) (B.model n) ℂ)‖ ≤ M
  rw [CStarRing.norm_mul_mem_unitary _ (B.map n g).2,
    CStarRing.norm_mem_unitary_mul _
      (conjTranspose_mem_unitaryGroup (B.map n g).2)]
  exact hMx n

/-- The conjugate-double matrix with its type fixed to the adjoint model.
This wrapper prevents semireducible finite-model instances from obscuring
that `B.adjoint.model n` is definitionally the doubled model. -/
def adjointMatrixSequence (B : OpAlmostRepresentation E)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ) (n : ℕ) :
    Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ := by
  change Matrix (doubleModel (B.model n)) (doubleModel (B.model n)) ℂ
  exact conjDouble (u n : Matrix (B.model n) (B.model n) ℂ)

theorem adjointMatrixSequence_mem_unitaryGroup
    (B : OpAlmostRepresentation E)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ) (n : ℕ) :
    adjointMatrixSequence B u n ∈
      Matrix.unitaryGroup (B.adjoint.model n) ℂ := by
  change conjDouble (u n : Matrix (B.model n) (B.model n) ℂ) ∈
    Matrix.unitaryGroup (doubleModel (B.model n)) ℂ
  exact conjDouble_mem_unitaryGroup (u n).2

theorem adjointMatrixSequence_mulVec_gammaRowVec
    (B : OpAlmostRepresentation E)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ) (n : ℕ)
    (X : Matrix (B.model n) (B.model n) ℂ) :
    adjointMatrixSequence B u n *ᵥ gammaRowVec B n X =
      gammaRowVec B n
        ((u n : Matrix (B.model n) (B.model n) ℂ) * X *
          (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  change conjDouble (u n : Matrix (B.model n) (B.model n) ℂ) *ᵥ rowVec X =
    rowVec ((u n : Matrix (B.model n) (B.model n) ℂ) * X *
      (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ)
  exact conjDouble_mulVec_rowVec _ _

/-- Almost multiplicativity makes adjoint action multiplicative modulo
Hilbert--Schmidt-null sequences. -/
theorem adjointSequence_mul_hs
    (B : OpAlmostRepresentation E) (g h : E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsUniformlyBounded B x) :
    HSSqVanishing B (fun n ↦
      adjointSequence B (g * h) x n -
        adjointSequence B g (adjointSequence B h x) n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n (g * h)
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h,
      mul_mem (B.map n g).2 (B.map n h).2⟩
  simpa [adjointSequence, u, v, Matrix.mul_assoc] using
    conjugation_hsSqVanishing_of_opNormVanishing u v x hbound
      (multiplicativeDefect_vanishing B g h)

/-- Almost multiplicativity makes inverse adjoint action anti-multiplicative
modulo Hilbert--Schmidt-null sequences. -/
theorem coadjointSequence_mul_hs
    (B : OpAlmostRepresentation E) (g h : E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsUniformlyBounded B x) :
    HSSqVanishing B (fun n ↦
      coadjointSequence B (g * h) x n -
        coadjointSequence B h (coadjointSequence B g x) n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n (g * h)).2⟩
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨((B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h)ᴴ,
      conjTranspose_mem_unitaryGroup (mul_mem (B.map n g).2 (B.map n h).2)⟩
  have hdef := OpNormVanishing.conjTranspose
    (B := B) (multiplicativeDefect_vanishing B g h)
  have hdef' : OpNormVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) - v n) := by
    simpa only [u, v, Matrix.conjTranspose_sub] using hdef
  simpa [coadjointSequence, u, v, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
    conjugation_hsSqVanishing_of_opNormVanishing u v x hbound hdef'

theorem adjointSequence_inv_hs
    (B : OpAlmostRepresentation E) (g : E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsUniformlyBounded B x) :
    HSSqVanishing B (fun n ↦
      adjointSequence B g⁻¹ x n - coadjointSequence B g x n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n g⁻¹
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n g).2⟩
  simpa [adjointSequence, coadjointSequence, u, v] using
    conjugation_hsSqVanishing_of_opNormVanishing u v x hbound
      (map_inv_vanishing B g)

theorem coadjointSequence_inv_hs
    (B : OpAlmostRepresentation E) (g : E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsUniformlyBounded B x) :
    HSSqVanishing B (fun n ↦
      coadjointSequence B g⁻¹ x n - adjointSequence B g x n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n g⁻¹).2⟩
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n g
  have hdef := OpNormVanishing.conjTranspose (B := B) (map_inv_vanishing B g)
  have hdef' : OpNormVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) - v n) := by
    simpa only [u, v, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose] using hdef
  simpa [adjointSequence, coadjointSequence, u, v] using
    conjugation_hsSqVanishing_of_opNormVanishing u v x hbound hdef'

theorem adjointSequence_one_hs
    (B : OpAlmostRepresentation E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsUniformlyBounded B x) :
    HSSqVanishing B (fun n ↦ adjointSequence B 1 x n - x n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n 1
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨1, by simp⟩
  simpa [adjointSequence, u, v] using
    conjugation_hsSqVanishing_of_opNormVanishing u v x hbound
      (map_one_vanishing B)

theorem coadjointSequence_one_hs
    (B : OpAlmostRepresentation E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsUniformlyBounded B x) :
    HSSqVanishing B (fun n ↦ coadjointSequence B 1 x n - x n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n 1 : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n 1).2⟩
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨1, by simp⟩
  have hdef := OpNormVanishing.conjTranspose (B := B) (map_one_vanishing B)
  have hdef' : OpNormVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) - v n) := by
    simpa only [u, v, Matrix.conjTranspose_sub, Matrix.conjTranspose_one] using hdef
  simpa [coadjointSequence, u, v] using
    conjugation_hsSqVanishing_of_opNormVanishing u v x hbound hdef'

/-- Elements whose coordinate adjoint and inverse-adjoint actions both
preserve every bounded asymptotic-commutant sequence. -/
def asymptoticCommutantStabilizer (B : OpAlmostRepresentation E)
    (iota : Γ →* E) : Subgroup E where
  carrier := {g | ∀ x, IsUniformlyBounded B x → IsAsymptoticCommutantOf B iota x →
    IsAsymptoticCommutantOf B iota (adjointSequence B g x) ∧
      IsAsymptoticCommutantOf B iota (coadjointSequence B g x)}
  one_mem' := by
    intro x hbound hx
    exact ⟨IsAsymptoticCommutant.congr_hs hx
        (adjointSequence_one_hs B x hbound).sub_symm,
      IsAsymptoticCommutant.congr_hs hx
        (coadjointSequence_one_hs B x hbound).sub_symm⟩
  mul_mem' := by
    intro g h hg hh x hbound hx
    have hhx := hh x hbound hx
    have hforward := hg (adjointSequence B h x)
      (IsUniformlyBounded.adjointSequence hbound) hhx.1
    have hbackward := hh (coadjointSequence B g x)
      (IsUniformlyBounded.coadjointSequence hbound)
      (hg x hbound hx).2
    exact ⟨IsAsymptoticCommutant.congr_hs hforward.1
        (adjointSequence_mul_hs B g h x hbound).sub_symm,
      IsAsymptoticCommutant.congr_hs hbackward.2
        (coadjointSequence_mul_hs B g h x hbound).sub_symm⟩
  inv_mem' := by
    intro g hg x hbound hx
    have hgx := hg x hbound hx
    exact ⟨IsAsymptoticCommutant.congr_hs hgx.2
        (adjointSequence_inv_hs B g x hbound).sub_symm,
      IsAsymptoticCommutant.congr_hs hgx.1
        (coadjointSequence_inv_hs B g x hbound).sub_symm⟩

/-- Conjugating the reverse displacement by the implementing unitary turns it
into the negative forward displacement. -/
theorem reverse_hsSqVanishing
    {B : OpAlmostRepresentation E}
    {C : KazhdanCompressionCore Γ E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsAsymptoticCommutant B C x) (γ : Γ) :
    HSSqVanishing B (fun n ↦
      x n - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
        x n * B.map n (C.iota γ)) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n (C.iota γ)
  have h := (hx γ).neg.unitary_conjugate (fun n ↦
    ⟨(u n : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (u n).2⟩)
  exact h.congr fun n ↦ by
    have huu : (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ * u n = 1 :=
      Unitary.star_mul_self_of_mem (u n).2
    have hux : (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ *
        ((u n : Matrix (B.model n) (B.model n) ℂ) * x n) = x n := by
      rw [← Matrix.mul_assoc, huu, one_mul]
    change (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          (-(x n - (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
            (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ)) *
          ((u n : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ =
        x n - (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n * u n
    rw [Matrix.conjTranspose_conjTranspose]
    noncomm_ring
    rw [huu, mul_one, hux]

/-- The Hermitian Kazhdan-average residual of an asymptotic-commutant
sequence is Hilbert--Schmidt null. -/
theorem laplacian_hsSqVanishing
    {B : OpAlmostRepresentation E}
    {C : KazhdanCompressionCore Γ E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsAsymptoticCommutant B C x)
    (S : Finset Γ) (_hone : 1 ∈ S) :
    HSSqVanishing B (fun n ↦
      (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            x n * (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          (x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            x n * B.map n (C.iota s))))) := by
  have hsum : HSSqVanishing B (fun n ↦ ∑ s ∈ S,
      ((x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          x n * (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        (x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          x n * B.map n (C.iota s)))) := by
    apply HSSqVanishing.finset_sum S
    intro s _
    exact (hx s).add (reverse_hsSqVanishing hx s)
  exact (hsum.smul (S.card : ℂ)⁻¹).smul (2 : ℂ)⁻¹

/-- Spectral capture for every bounded asymptotic-commutant sequence. -/
theorem capture_vanishing
    {B : OpAlmostRepresentation E}
    {C : KazhdanCompressionCore Γ E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x)
    {S : Finset Γ} (hone : 1 ∈ S) {θ : ℝ} (hθ : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      MarkedCompressionVectorChain.vecMass
        ((1 - cornerProjection B C S θ n) *ᵥ gammaRowVec B n (x n)) ≤
          ε * Fintype.card (B.model n) := by
  classical
  obtain ⟨M, hM, hMx⟩ := hbound
  intro ε hε
  have hgap : 0 < 1 - θ := by linarith
  let η : ℝ := (1 - θ) * ε / (M ^ 2 + 1)
  have hden : 0 < M ^ 2 + 1 := by positivity
  have hη : 0 < η := div_pos (mul_pos hgap hε) hden
  obtain ⟨N, hN⟩ := laplacian_hsSqVanishing hx S hone (η ^ 2) (sq_pos_of_pos hη)
  refine ⟨N, fun n hn ↦ ?_⟩
  let R : Matrix (B.model n) (B.model n) ℂ :=
    (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
      ((x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          x n * (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        (x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          x n * B.map n (C.iota s))))
  let H := hermitianAverage (gammaAdjoint B C) S n
  let P := cornerProjection B C S θ n
  let ξ := gammaRowVec B n (x n)
  have hresidVec : ξ - H *ᵥ ξ = gammaRowVec B n R := by
    simpa [R, H, ξ] using matrix_laplacian_matVec B C S hone n (x n)
  have hR : hsNormSq (B.model n) R ≤ η ^ 2 := by
    simpa [R] using hN n hn
  have hcard : (0 : ℝ) < Fintype.card (B.model n) := by
    exact_mod_cast B.modelNonempty n
  have hresidMass :
      ∑ i : (gammaAdjoint B C).model n,
          Complex.normSq ((ξ - H *ᵥ ξ) i) ≤
        Fintype.card (B.model n) * η ^ 2 := by
    rw [hresidVec, sum_normSq_gammaRowVec]
    unfold hsNormSq at hR
    rw [div_le_iff₀ hcard] at hR
    simpa [mul_comm] using hR
  have hxiMass :
      ∑ i : (gammaAdjoint B C).model n, Complex.normSq (ξ i) ≤
        Fintype.card (B.model n) * M ^ 2 := by
    rw [show ξ = gammaRowVec B n (x n) by rfl, sum_normSq_gammaRowVec]
    exact (sum_normSq_le_card_mul_sq _ _).trans (by gcongr; exact hMx n)
  have henergy : (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
      ((1 - θ) * ε) * Fintype.card (B.model n) := by
    have hamgm := re_star_dotProduct_le hη ξ (ξ - H *ᵥ ξ)
    calc
      (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
          (2 : ℝ)⁻¹ *
            (η * ∑ i, Complex.normSq (ξ i) +
              η⁻¹ * ∑ i, Complex.normSq ((ξ - H *ᵥ ξ) i)) := hamgm
      _ ≤ (2 : ℝ)⁻¹ *
            (η * (Fintype.card (B.model n) * M ^ 2) +
              η⁻¹ * (Fintype.card (B.model n) * η ^ 2)) := by gcongr
      _ ≤ ((1 - θ) * ε) * Fintype.card (B.model n) := by
        dsimp [η]
        field_simp
        nlinarith [sq_nonneg M]
  have hcapture := capture_vec H
    (by simpa [H, Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using
      hermitianAverage_conjTranspose (gammaAdjoint B C) S n)
    θ 0 hθ.le (by positivity)
    (by simpa [H] using norm_hermitianAverage_le_one (gammaAdjoint B C) S n) ξ
  have hbelow : spectralBelow H
      (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ = 1 - P := rfl
  rw [hbelow, zero_mul, add_zero] at hcapture
  have hmul : (1 - θ) *
      MarkedCompressionVectorChain.vecMass ((1 - P) *ᵥ ξ) ≤
        (1 - θ) * (ε * Fintype.card (B.model n)) :=
    hcapture.trans (by simpa [mul_assoc] using henergy)
  exact le_of_mul_le_mul_left hmul hgap

private theorem transport_of_leakage
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x)
    (S : Finset Γ) (kappa theta : ℝ)
    (hone : 1 ∈ S) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hkappaOne : kappa ≤ 1)
    (hpair : IsKazhdanPair.{0, 0} Γ S kappa)
    (htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta)
    (htheta1 : theta < 1)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ)
    (hleak : ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      ‖(1 - cornerProjection B C S theta n) *
        (adjointMatrixSequence B u n * cornerProjection B C S theta n *
          (adjointMatrixSequence B u n)ᴴ)‖ ≤ epsilon) :
    IsAsymptoticCommutant B C (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  classical
  obtain ⟨M, hM, hMx⟩ := hbound
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  intro γ ε hε
  let q : ℝ := min 1 (ε / (40 * (M ^ 2 + 1)))
  have hden : 0 < 40 * (M ^ 2 + 1) := by positivity
  have hq : 0 < q := lt_min (by norm_num) (div_pos hε hden)
  obtain ⟨Nfix, hNfix⟩ := displacement_vanishing B C theta hpair hone hkappaOne
    hsymm hgen htheta4 γ q hq
  obtain ⟨Nrev, hNrev⟩ := hleak q hq
  obtain ⟨Ncap, hNcap⟩ := capture_vanishing hx ⟨M, hM, hMx⟩ hone htheta1 q hq
  refine ⟨max Nfix (max Nrev Ncap), fun n hn ↦ ?_⟩
  let Ua : Matrix (B.model n) (B.model n) ℂ := B.map n (C.iota γ)
  let Ut : Matrix (B.model n) (B.model n) ℂ := u n
  let X : Matrix (B.model n) (B.model n) ℂ := x n
  let P : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    cornerProjection B C S theta n
  let Ta : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    B.adjoint.map n (C.iota γ)
  let Tt : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    adjointMatrixSequence B u n
  have hfix : ‖(Ta - 1) * P‖ ≤ q := by
    simpa [Ta, Ua, P, gammaAdjoint] using
      hNfix n ((le_max_left _ _).trans hn)
  have hrev : ‖(1 - P) * (Tt * P * Ttᴴ)‖ ≤ q := by
    simpa [Tt, P, Ut] using
      hNrev n ((le_max_left Nrev Ncap).trans
        ((le_max_right Nfix (max Nrev Ncap)).trans hn))
  have hcap := hNcap n ((le_max_right Nrev Ncap).trans
    ((le_max_right Nfix (max Nrev Ncap)).trans hn))
  have hchain := MarkedCompressionVectorChain.transported_displacement_le
    (Y := B.adjoint.model n) (B.adjoint.modelNonempty n)
    (cornerProjection_isOrthogonalProjection B C S theta n)
    (show Tt ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ by
      exact adjointMatrixSequence_mem_unitaryGroup B u n)
    (show Ta ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ by
      exact (B.adjoint.map n (C.iota γ)).2)
    hfix hrev hcap
  have hxmass : MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) ≤
      Fintype.card (B.model n) * M ^ 2 := by
    rw [MarkedCompressionVectorChain.vecMass, sum_normSq_gammaRowVec]
    exact (sum_normSq_le_card_mul_sq _ _).trans (by gcongr; exact hMx n)
  have hqone : q ≤ 1 := min_le_left _ _
  have hqeps : q * (40 * (M ^ 2 + 1)) ≤ ε := by
    calc
      q * (40 * (M ^ 2 + 1)) ≤
          (ε / (40 * (M ^ 2 + 1))) * (40 * (M ^ 2 + 1)) := by
        gcongr
        exact min_le_right _ _
      _ = ε := by field_simp
  have hmass :
      MarkedCompressionVectorChain.vecMass
        (Ta *ᵥ (Tt *ᵥ gammaRowVec B n X) -
          Tt *ᵥ gammaRowVec B n X) ≤
        (2 * q ^ 2 + 16 * q ^ 2) *
            MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) +
          16 * (q * Fintype.card (B.model n)) :=
    hchain
  have hmass' :
      MarkedCompressionVectorChain.vecMass
        (Ta *ᵥ (Tt *ᵥ gammaRowVec B n X) -
          Tt *ᵥ gammaRowVec B n X) ≤
        Fintype.card (B.model n) *
          (18 * q ^ 2 * M ^ 2 + 16 * q) := by
    calc
      _ ≤ (2 * q ^ 2 + 16 * q ^ 2) *
            MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) +
          16 * (q * Fintype.card (B.model n)) := hmass
      _ ≤ (2 * q ^ 2 + 16 * q ^ 2) *
            (Fintype.card (B.model n) * M ^ 2) +
          16 * (q * Fintype.card (B.model n)) := by gcongr
      _ = Fintype.card (B.model n) *
          (18 * q ^ 2 * M ^ 2 + 16 * q) := by ring
  have hsmall : 18 * q ^ 2 * M ^ 2 + 16 * q ≤ ε := by
    calc
      18 * q ^ 2 * M ^ 2 + 16 * q ≤
          q * (40 * (M ^ 2 + 1)) := by
        nlinarith [hM, hq.le, hqone, sq_nonneg M,
          mul_nonneg hq.le (sq_nonneg M)]
      _ ≤ ε := hqeps
  have hcardR : (0 : ℝ) < Fintype.card (B.model n) := by
    exact_mod_cast B.modelNonempty n
  let D : Matrix (B.model n) (B.model n) ℂ := Ut * X * Utᴴ
  let E' : Matrix (B.model n) (B.model n) ℂ := Ua * D * Uaᴴ
  have hTt : Tt *ᵥ gammaRowVec B n X = gammaRowVec B n D := by
    simpa [Tt, Ut, D] using
      adjointMatrixSequence_mulVec_gammaRowVec B u n X
  have hTa : Ta *ᵥ gammaRowVec B n D = gammaRowVec B n E' := by
    simpa [Ta, Ua, E', gammaAdjoint] using
      gammaAdjoint_mulVec_gammaRowVec B C n γ D
  have hvec : Ta *ᵥ (Tt *ᵥ gammaRowVec B n X) -
      Tt *ᵥ gammaRowVec B n X = gammaRowVec B n (E' - D) := by
    rw [hTt, hTa, ← gammaRowVec_sub]
  change hsNormSq (B.model n)
      (Ut * X * Utᴴ - Ua * (Ut * X * Utᴴ) * Uaᴴ) ≤ ε
  rw [hsNormSq]
  rw [div_le_iff₀ hcardR]
  calc
    (∑ i : B.model n, ∑ j : B.model n,
        Complex.normSq
          ((Ut * X * Utᴴ - Ua * (Ut * X * Utᴴ) * Uaᴴ) i j)) =
        MarkedCompressionVectorChain.vecMass
          (Ta *ᵥ (Tt *ᵥ gammaRowVec B n X) -
            Tt *ᵥ gammaRowVec B n X) := by
      rw [hvec, MarkedCompressionVectorChain.vecMass,
        sum_normSq_gammaRowVec]
      refine Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show (Ut * X * Utᴴ - Ua * (Ut * X * Utᴴ) * Uaᴴ) i j =
          -((E' - D) i j) by simp [E', D],
        Complex.normSq_neg]
    _ ≤ Fintype.card (B.model n) *
        (18 * q ^ 2 * M ^ 2 + 16 * q) := hmass'
    _ ≤ Fintype.card (B.model n) * ε :=
      mul_le_mul_of_nonneg_left hsmall hcardR.le
    _ = ε * Fintype.card (B.model n) := by ring

/-- **Forward Kazhdan transport.**  A one-sided compressor preserves every
uniformly bounded normalized-Hilbert--Schmidt asymptotic commutant sequence. -/
theorem transport
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, hkappa, hkappaOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair C.kazhdan
  let theta : ℝ := ((1 - kappa ^ 2 / (4 * S.card)) + 1) / 2
  have htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta := by
    dsimp [theta]
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  have htheta1 : theta < 1 := by
    dsimp [theta]
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  apply transport_of_leakage B C x hx hbound S kappa theta hone hsymm hgen
    hkappaOne hpair htheta4 htheta1 (fun n ↦ B.map n C.t)
  intro epsilon hepsilon
  simpa [movedProjection, adjointMatrixSequence] using
    one_sub_corner_mul_moved_vanishing B C theta hpair hone hkappaOne
      hsymm hgen htheta4 htheta1 epsilon hepsilon

/-- **Reverse Kazhdan transport.**  Finite-coordinate rank balance upgrades
the one-sided compressor to invariance under the inverse adjoint action. -/
theorem transport_star
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, hkappa, hkappaOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair C.kazhdan
  let theta : ℝ := ((1 - kappa ^ 2 / (4 * S.card)) + 1) / 2
  have htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta := by
    dsimp [theta]
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  have htheta1 : theta < 1 := by
    dsimp [theta]
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  let ustar : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n C.t).2⟩
  have hleak : ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      ‖(1 - cornerProjection B C S theta n) *
        (adjointMatrixSequence B ustar n * cornerProjection B C S theta n *
          (adjointMatrixSequence B ustar n)ᴴ)‖ ≤ epsilon := by
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := one_sub_moved_mul_corner_vanishing B C theta hpair
      hone hkappaOne hsymm hgen htheta4 htheta1 epsilon hepsilon
    refine ⟨N, fun n hn ↦ ?_⟩
    let T : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
      conjDouble (B.map n C.t)
    let P : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
      cornerProjection B C S theta n
    have hT : T ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ :=
      conjDouble_mem_unitaryGroup (B.map n C.t).2
    have hTstar : Tᴴ ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ :=
      conjTranspose_mem_unitaryGroup hT
    have hTstarT : Tᴴ * T = 1 := Unitary.star_mul_self_of_mem hT
    have hcancel : ∀ Y : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ,
        Tᴴ * (T * Y) = Y := by
      intro Y
      rw [← Matrix.mul_assoc, hTstarT, one_mul]
    have hraw : ‖(1 - T * P * Tᴴ) * P‖ ≤ epsilon := by
      simpa [T, P, movedProjection] using hN n hn
    have hfactor :
        (1 - P) * (Tᴴ * P * T) = Tᴴ * ((1 - T * P * Tᴴ) * P) * T := by
      noncomm_ring
      rw [hcancel]
    have htarget : ‖(1 - P) * (Tᴴ * P * T)‖ ≤ epsilon := by
      rw [hfactor, CStarRing.norm_mul_mem_unitary _ hT,
        CStarRing.norm_mem_unitary_mul _ hTstar]
      exact hraw
    simpa [T, P, ustar, adjointMatrixSequence,
      conjDouble_conjTranspose] using htarget
  have htransport := transport_of_leakage B C x hx hbound S kappa theta hone
    hsymm hgen hkappaOne hpair htheta4 htheta1 ustar hleak
  simpa [ustar, Matrix.conjTranspose_conjTranspose] using htransport

/-- A one-sided compressor acts as a two-sided symmetry of the bounded
normalized-Hilbert--Schmidt asymptotic commutant. -/
theorem transport_both
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
      IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) :=
  ⟨transport B C x hx hbound, transport_star B C x hx hbound⟩

/-- The compression core attached to an arbitrary one-sided compressor.  The
root is irrelevant for asymptotic-commutant transport and is chosen to be the
identity. -/
def coreOfCompressor (iota : Γ →* E) (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (s : E) (hs : s ∈ compressionSet iota.range) : KazhdanCompressionCore Γ E where
  iota := iota
  t := s
  c := 1
  kazhdan := hkazhdan
  compresses gamma := by
    obtain ⟨delta, hdelta⟩ := hs (iota gamma) ⟨gamma, rfl⟩
    exact ⟨delta, hdelta.symm⟩
  comm_c gamma := Commute.one_left _

/-- Every one-sided compressor, not merely a distinguished stable letter,
acts in both directions on the bounded asymptotic commutant. -/
theorem compressionSet_transport_both
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : ∀ gamma : Γ, HSSqVanishing B (fun n ↦
      x n - (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
        x n * (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ))
    (hbound : IsUniformlyBounded B x)
    {s : E} (hs : s ∈ compressionSet iota.range) :
    IsAsymptoticCommutantOf B iota (adjointSequence B s x) ∧
      IsAsymptoticCommutantOf B iota (coadjointSequence B s x) := by
  let C := coreOfCompressor iota hkazhdan s hs
  have hxC : IsAsymptoticCommutant B C x := by
    change IsAsymptoticCommutantOf B iota x
    exact hx
  have htransport := transport_both B C x hxC hbound
  change IsAsymptoticCommutantOf B C.iota (adjointSequence B C.t x) ∧
    IsAsymptoticCommutantOf B C.iota (coadjointSequence B C.t x) at htransport
  change IsAsymptoticCommutantOf B iota (adjointSequence B s x) ∧
    IsAsymptoticCommutantOf B iota (coadjointSequence B s x)
  exact htransport

/-- Every one-sided compressor belongs to the asymptotic-commutant
stabilizer. -/
theorem compressionSet_subset_asymptoticCommutantStabilizer
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ) :
    compressionSet iota.range ⊆ asymptoticCommutantStabilizer B iota := by
  intro s hs x hbound hx
  exact compressionSet_transport_both B iota hkazhdan x hx hbound hs

/-- **All-compressors Kazhdan transport.**  The group generated by every
one-sided compressor acts as a two-sided symmetry of the entire bounded
asymptotic commutant. -/
theorem compressionGroup_le_asymptoticCommutantStabilizer
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ) :
    compressionGroup iota.range ≤ asymptoticCommutantStabilizer B iota := by
  rw [compressionGroup, Subgroup.closure_le]
  exact compressionSet_subset_asymptoticCommutantStabilizer B iota hkazhdan

/-- Pointwise form of the all-compressors transport theorem.  The ambient
group is arbitrary, as in the manuscript's Corollary 4.6. -/
theorem compressionGroup_transport_both :
    ∀ {Γ₀ : Type} {E₀ : Type u} [Group Γ₀] [Group E₀]
    (B : OpAlmostRepresentation E₀) (iota : Γ₀ →* E₀)
    (_hkazhdan : HasKazhdanPropertyT.{0, 0} Γ₀)
    {g : E₀} (_hg : g ∈ compressionGroup iota.range)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (_hbound : IsUniformlyBounded B x)
    (_hx : IsAsymptoticCommutantOf B iota x),
    IsAsymptoticCommutantOf B iota (adjointSequence B g x) ∧
      IsAsymptoticCommutantOf B iota (coadjointSequence B g x) :=
  by
    intro Γ₀ E₀ _ _ B iota hkazhdan g hg x hbound hx
    exact compressionGroup_le_asymptoticCommutantStabilizer B iota hkazhdan hg
      x hbound hx

end KazhdanAsymptoticCommutant
end GroupApproximation
