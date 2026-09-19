import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Sofic.AdjointMatrix
import GroupApproximation.Sofic.HyperlinearScalar

/-!
# The ambient of the ultraproduct proof of `thm:kazhdan-transport`

This file certifies steps **KT.01**, **KT.03**, part of **KT.04**, and
**KT.05** of the ultraproduct proof printed in `non_mf_groups_exist.tex` for
the theorem labelled `thm:kazhdan-transport`, captioned *Kazhdan transport of
Hilbert--Schmidt asymptotic commutants*.  The paragraphs being formalized are
the ones opening `\emph{The adjoint model.}` and `\emph{The ultraproduct.}`.
Line numbers are deliberately not cited: the manuscript is under concurrent
revision and only the label and the quoted sentences are stable.

* **KT.01.**  `K_n = L²(M_{d_n}(ℂ), tr_{d_n})` is the matrix algebra with the
  normalized Hilbert--Schmidt inner product; in row-major coordinates it is
  `ℂ^{Y_n × Y_n}` with the Euclidean mass divided by `card Y_n`
  (`kt_01_hsNormSq_rowVec`).  The conjugation `Ad U(ξ) = U ξ U*` is the matrix
  `conjDouble U` in those coordinates (`kt_01_adjoint_action`), it preserves
  the normalized Hilbert--Schmidt norm when `U` is unitary
  (`kt_01_hsNormSq_adjoint`), and `g ↦ Ad U_n(g)` is again an operator-norm
  asymptotic representation, with a dimension-free defect estimate
  (`kt_01_adjoint_asymptoticallyMultiplicative`).  The underlying
  construction is the repo's `OpAlmostRepresentation.adjoint`.

* **KT.03.**  `B(K_n)` is again a matrix algebra, on the doubled index
  `Y_n × Y_n`, so `B_ω = ∏_ω B(K_n)` is the repo's `NormMatrixCStarCorona` on
  the doubled models (`adjointNormCorona`), a genuine unital complex C-star
  algebra.  The manuscript's free ultrafilter `ω` is realized as the cofinite
  filter; this is legitimate because the printed proof first extracts an
  infinite set `I` of failing indices and only then chooses `ω ∋ I`.

* **KT.04.**  Only the two consequences of faithfulness that the rest of the
  proof consumes are formalized here: the corona norm is the limsup of the
  coordinate operator norms (`kt_04_norm_eq_limsup`), and an inclusion of
  ranges, written `(1 - q) p = 0`, is exactly the pair of absorption
  identities `q p = p`, `p q = p` (`kt_04_absorb_of_range_le`).  The
  Hilbert-space ultraproduct `K_ω` itself is **not** constructed here.

* **KT.05.**  `π(g) = [Ad U_n(g)]_ω` is a genuine group homomorphism into
  `U(B_ω)` (`adjointCoronaHom`).  This is where the asymptotic
  multiplicativity of `U_n` is consumed and becomes exact: the multiplicative
  defect lies in the `c₀` ideal, hence dies in the quotient.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator ENNReal

universe u v

noncomputable section

/-! ## KT.01 the adjoint model -/

/-- **KT.01.**  Row-major vectorization identifies the normalized
Hilbert--Schmidt norm of `M_Y(ℂ)` with the Euclidean mass on `ℂ^{Y × Y}`
divided by `card Y`.  This is the manuscript's
`K_n = L²(M_{d_n}(ℂ), tr_{d_n})`. -/
theorem kt_01_hsNormSq_rowVec (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    (∑ p : Y × Y, Complex.normSq (rowVec A p)) / (Fintype.card Y : ℝ)
      = hsNormSq Y A := by
  rw [sum_normSq_rowVec]
  rfl

/-- **KT.01.**  In row-major coordinates the conjugation `ξ ↦ U ξ U*` is the
matrix `conjDouble U`. -/
theorem kt_01_adjoint_action (Y : FiniteModel) (U xi : Matrix Y Y ℂ) :
    conjDouble U *ᵥ rowVec xi = rowVec (U * xi * Uᴴ) :=
  conjDouble_mulVec_rowVec U xi

/-- The conjugate transpose of a unitary matrix is unitary. -/
theorem conjTranspose_mem_unitaryGroup_of_mem (Y : FiniteModel)
    {U : Matrix Y Y ℂ} (hU : U ∈ Matrix.unitaryGroup Y ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
  have h : Uᴴ * U = 1 := by
    have h0 := hU
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h0
    exact h0
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact h

/-- **KT.01.**  `Ad U` is a unitary of `K_n`: the normalized Hilbert--Schmidt
norm is invariant under `ξ ↦ U ξ U*` for unitary `U`. -/
theorem kt_01_hsNormSq_adjoint (Y : FiniteModel) {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y)
    (xi : Matrix Y Y ℂ) :
    hsNormSq Y (U * xi * Uᴴ) = hsNormSq Y xi := by
  rw [hsNormSq_mul_right Y (conjTranspose_mem_unitaryGroup_of_mem Y hU)
      (U * xi),
    hsNormSq_mul_left Y hU hY xi]

variable {H : Type u} [Group H]

/-- **KT.01.**  The matrix of `Ad U_n(g)` in row-major coordinates is
`conjDouble (U_n g)`. -/
theorem kt_01_adjoint_map (A : OpAlmostRepresentation H) (n : ℕ) (g : H) :
    (A.adjoint.map n g :
        Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ) =
      conjDouble (A.map n g) :=
  OpAlmostRepresentation.adjoint_map A n g

/-- **KT.01.**  `g ↦ Ad U_n(g)` is an operator-norm asymptotic representation
on the matrix Hilbert spaces `K_n`.  The estimate behind it is dimension-free:
the conjugate double is `2`-Lipschitz on the unitary group
(`l2_opNorm_conjDouble_sub_le_two`), so operator-norm defects transfer with no
dimension loss.  This is the manuscript's "finite-stage form of the
`π ⊗ π̄` construction". -/
theorem kt_01_adjoint_asymptoticallyMultiplicative
    (A : OpAlmostRepresentation H) (g h : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ‖(A.adjoint.map n (g * h) :
            Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ) -
          (A.adjoint.map n g :
            Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ) *
            (A.adjoint.map n h :
              Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ)‖ ≤ ε :=
  A.adjoint.asymptoticallyMultiplicative g h ε hε

/-- Every finite model carried by an operator-norm almost representation is
nonempty.  Deliberately a theorem rather than an instance: it is fed to the
corona constructions by `letI`, and `Nonempty` is a `Prop`, so the choice is
irrelevant downstream. -/
theorem OpAlmostRepresentation.nonempty_model
    (A : OpAlmostRepresentation H) (n : ℕ) : Nonempty (A.model n) :=
  Fintype.card_pos_iff.mp (A.modelNonempty n)

/-! ## KT.03 the norm ultraproduct `B_ω` -/

/-- **KT.03.**  The norm ultraproduct `∏_ω B(K_n)` of the operator algebras of
the finite-stage Hilbert spaces.  Because `K_n` is finite dimensional,
`B(K_n)` is itself a matrix algebra, so this is the repo's norm-matrix C-star
corona; in particular it is a unital complex C-star algebra by
`normMatrixCStarCoronaCStarAlgebra`. -/
abbrev opAlmostRepNormCorona (A : OpAlmostRepresentation H)
    [∀ n, Nonempty (A.model n)] : Type :=
  NormMatrixCStarCorona (fun n ↦ A.model n)

/-- **KT.03 at the adjoint model.**  `B_ω = ∏_ω B(K_n)`, the ambient algebra
of the manuscript's ultraproduct argument.  The nonemptiness instance is
always available: supply it with
`letI : ∀ n, Nonempty (A.adjoint.model n) := A.adjoint.nonempty_model`. -/
abbrev adjointNormCorona (A : OpAlmostRepresentation H)
    [∀ n, Nonempty (A.adjoint.model n)] : Type :=
  NormMatrixCStarCorona (fun n ↦ A.adjoint.model n)

/-! ## KT.04 what faithfulness is used for

The manuscript proves that the action of `B_ω` on `K_ω` is faithful and then
uses that fact twice: to know that the corona norm sees the coordinate
operator norms, and to convert an inclusion of ranges into an inequality of
projections.  Both consequences are recorded here.  The Hilbert-space
ultraproduct `K_ω` is not constructed in this file.
-/

/-- **KT.04 (norm form).**  The corona norm of a class is the limsup of the
coordinate operator norms.  Equivalently: a class is nonzero exactly when its
coordinates keep a positive operator norm along the filter, which is the
quantitative content of the manuscript's faithfulness computation
`‖A[ξ_n]_ω‖ = lim_ω ‖A_n ξ_n‖ = lim_ω ‖A_n‖`. -/
theorem kt_04_norm_eq_limsup (X : ℕ → Type v) [∀ n, Fintype (X n)]
    [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (a : BoundedMatrixSequence X) :
    ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X cofinite) a‖ =
      Filter.limsup (fun n ↦ ‖a n‖) atTop :=
  (norm_filterMatrixCorona_mk_eq_limsup X cofinite a).trans
    (by rw [Nat.cofinite_eq_atTop])

/-- **KT.04 (projection form).**  "`ran p ⊆ ran q`", written algebraically as
`(1 - q) p = 0`, is exactly the pair of absorption identities `q p = p` and
`p q = p`, which is the form of `p ≤ q` consumed by
`ProperProjectionCompression`. -/
theorem kt_04_absorb_of_range_le {R : Type*} [Ring R] [StarRing R] {p q : R}
    (hp : star p = p) (hq : star q = q) (h : (1 - q) * p = 0) :
    q * p = p ∧ p * q = p := by
  have h1 : q * p = p := by
    have hsub := h
    rw [sub_mul, one_mul, sub_eq_zero] at hsub
    exact hsub.symm
  refine ⟨h1, ?_⟩
  have h2 := congrArg star h1
  rw [star_mul, hp, hq] at h2
  exact h2

/-- The converse reading, for completeness: the absorption identity `q p = p`
says that `1 - q` annihilates `p`. -/
theorem kt_04_range_le_of_absorb {R : Type*} [Ring R] {p q : R}
    (h : q * p = p) : (1 - q) * p = 0 := by
  rw [sub_mul, one_mul, h, sub_self]

/-! ## KT.05 the representation into `U(B_ω)` -/

section CoronaHom

variable (A : OpAlmostRepresentation H) [∀ n, Nonempty (A.model n)]

/-- **The multiplicative defect dies in the corona.**  This is the single
analytic input of KT.05: the operator-norm defect `U_n(gh) - U_n(g)U_n(h)`
tends to zero, hence lies in the `c₀` ideal, hence is invisible in the
quotient. -/
theorem opAlmostRepCorona_mul (g h : H) :
    unitarySequenceToCorona A.model (fun n ↦ A.map n (g * h)) =
      unitarySequenceToCorona A.model (fun n ↦ A.map n g * A.map n h) := by
  have hzero : normMatrixCStarCoronaMk (fun n ↦ A.model n)
      (unitarySequenceBounded A.model (fun n ↦ A.map n (g * h)) -
        unitarySequenceBounded A.model
          (fun n ↦ A.map n g * A.map n h)) = 0 := by
    rw [normMatrixCStarCoronaMk_eq_zero_iff]
    show Tendsto (fun n ↦
        ‖(unitarySequenceBounded A.model (fun n ↦ A.map n (g * h)) -
          unitarySequenceBounded A.model
            (fun n ↦ A.map n g * A.map n h)) n‖) cofinite (nhds 0)
    rw [Nat.cofinite_eq_atTop, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Real.dist_eq, sub_zero, abs_norm]
    have hcoord :
        (unitarySequenceBounded A.model (fun n ↦ A.map n (g * h)) -
            unitarySequenceBounded A.model
              (fun n ↦ A.map n g * A.map n h)) n =
          (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
              (A.map n h : Matrix (A.model n) (A.model n) ℂ) := rfl
    rw [hcoord]
    exact lt_of_le_of_lt (hN n hn) (by linarith)
  rw [map_sub, sub_eq_zero] at hzero
  exact Subtype.ext hzero

/-- **KT.05.**  `π : H → U(B_ω)`, `π(g) = [U_n(g)]_ω`, is a genuine group
homomorphism.  Asymptotic multiplicativity of `(U_n)` is consumed here and
becomes exact multiplicativity in the quotient. -/
def opAlmostRepCoronaHom :
    H →* unitary (NormMatrixCStarCorona (fun n ↦ A.model n)) :=
  MonoidHom.mk' (fun g ↦ unitarySequenceToCorona A.model (fun n ↦ A.map n g))
    (fun g h ↦ by
      show unitarySequenceToCorona A.model (fun n ↦ A.map n (g * h)) =
        unitarySequenceToCorona A.model (fun n ↦ A.map n g) *
          unitarySequenceToCorona A.model (fun n ↦ A.map n h)
      rw [opAlmostRepCorona_mul A g h]
      exact map_mul (unitarySequenceToCorona A.model)
        (fun n ↦ A.map n g) (fun n ↦ A.map n h))

@[simp] theorem opAlmostRepCoronaHom_apply (g : H) :
    opAlmostRepCoronaHom A g =
      unitarySequenceToCorona A.model (fun n ↦ A.map n g) := rfl

end CoronaHom

/-- **KT.05 at the adjoint model.**  `π(g) = [Ad U_n(g)]_ω` is a group
homomorphism `H → U(B_ω)`.  This is the manuscript's

> Asymptotic multiplicativity makes `π : H → U(B_ω)`,
> `π(g) = [Ad U_n(g)]_ω`, a homomorphism.

The nonemptiness instance is always available: supply it with
`letI : ∀ n, Nonempty (A.adjoint.model n) := A.adjoint.nonempty_model`. -/
def adjointCoronaHom (A : OpAlmostRepresentation H)
    [∀ n, Nonempty (A.adjoint.model n)] :
    H →* unitary (NormMatrixCStarCorona (fun n ↦ A.adjoint.model n)) :=
  opAlmostRepCoronaHom A.adjoint

@[simp] theorem adjointCoronaHom_apply (A : OpAlmostRepresentation H)
    [∀ n, Nonempty (A.adjoint.model n)] (g : H) :
    adjointCoronaHom A g =
      unitarySequenceToCorona A.adjoint.model
        (fun n ↦ A.adjoint.map n g) := rfl

end

end GroupApproximation
