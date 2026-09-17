import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaClass
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work, BDL Proposition 1.5: the corner of a central involution

Census row `9e2046c330c8`, `non_mf_groups_exist.tex` lines 351--353:

> Bachner--Dogon--Lubotzky showed that for groups of Deligne type,
> operator--Hilbert--Schmidt stability would imply that the group is not
> MF~\cite[Proposition~1.5]{BDL}.

This file carries the operator-algebraic half of the proof. It needs neither
stability nor residual finiteness.

## Statement

Let `Γ` be a countable group and `ρ : Γ → U(𝒬_X)` an injective homomorphism
into the unitary group of a norm matrix corona. Let `J ≠ 1` be central with
`J² = 1`. Then there is an operator-norm asymptotic homomorphism
`V_k : Γ → U(d_k)` with `d_k > 0` along which `J` is asymptotically `−1`:
`‖V_k(J) + 1‖_op → 0`.

## Proof plan

1. `u = ρ(J)` is a unitary with `u² = 1`, hence self-adjoint. The element
   `q = ½(1 − u)` is a projection (`star q = q`, `q² = q`).
2. `q ≠ 0`. Otherwise `u = 1 = ρ(1)`, and injectivity gives `J = 1`.
3. `q` commutes with `ρ(Γ)`, because `u` does (`J` is central).
4. The formalized `lem:central-corona-corner`
   (`manuscriptPrintedCentralCoronaCorner`) applies to `(ρ, q)`. It returns:
   * a subsequence `φ`;
   * a projection lift `Q` of `q`;
   * corner models `r_k` with isometric additive identifications `J_k`, where
     `J_k(1) = Q_{φ k}`;
   * an operator-norm asymptotic homomorphism `W_k : Γ → U(r_k)`;
   * lifts `amb g = (J_k W_k(g))_k` whose corona classes are the coordinate
     restrictions of `q ρ(g)`.
5. `q u = ½(u − u²) = ½(u − 1) = −q`. For `g = J` the closing equation reads
   `[amb J] = −[restrict Q]`, so `[amb J + restrict Q] = 0`. The corona zero
   criterion gives `‖J_k W_k(J) + Q_{φ k}‖ → 0`. Since
   `J_k W_k(J) + Q_{φ k} = J_k (W_k(J) + 1)` and `J_k` is isometric, this is
   `‖W_k(J) + 1‖ → 0`.
6. Reindex `r_k` to `Fin |r_k|` along `Fintype.equivFin`
   (`unitaryReindexEquiv`). This preserves operator norms, so both the defect
   limit and `‖V_k(J) + 1‖ → 0` transfer.

The scalar computations of steps 1, 2, 3 and 5 are proved once over a generic
complex algebra and applied at the corona with `exact`, following
`CollapsePrintedCorollary`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedBDL

open Filter Topology
open scoped Matrix.Norms.L2Operator

noncomputable section

section ScalarHelpers

variable {A : Type*} [Ring A] [Module ℂ A]
  [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]

/-- `½(1 − u)` is idempotent for an involution `u`. -/
theorem bdl_half_one_sub_idempotent {u : A} (huu : u * u = 1) :
    ((2 : ℂ)⁻¹ • (1 - u)) * ((2 : ℂ)⁻¹ • (1 - u)) = (2 : ℂ)⁻¹ • (1 - u) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hexp : (1 - u) * (1 - u) = 1 - u - u + u * u := by noncomm_ring
  rw [hexp, huu]
  have h2 : (1 : A) - u - u + 1 = (2 : ℂ) • (1 - u) := by
    rw [two_smul ℂ]
    abel
  rw [h2, smul_smul]
  have hc : (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * 2 = (2 : ℂ)⁻¹ := by norm_num
  rw [hc]

/-- For an involution `u`, the projection `½(1 − u)` absorbs `u` as `−1`. -/
theorem bdl_half_one_sub_mul_self {u : A} (huu : u * u = 1) :
    ((2 : ℂ)⁻¹ • (1 - u)) * u = -((2 : ℂ)⁻¹ • (1 - u)) := by
  rw [smul_mul_assoc, sub_mul, one_mul, huu, ← smul_neg, neg_sub]

/-- Whatever commutes with `u` commutes with `½(1 − u)`. -/
theorem bdl_mul_half_one_sub_comm {v u : A} (h : v * u = u * v) :
    v * ((2 : ℂ)⁻¹ • (1 - u)) = ((2 : ℂ)⁻¹ • (1 - u)) * v := by
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sub, mul_one, sub_mul, one_mul, h]

/-- `½(1 − u) = 0` forces `u = 1`. -/
theorem bdl_eq_one_of_half_one_sub_eq_zero {u : A}
    (h : (2 : ℂ)⁻¹ • (1 - u) = 0) : u = 1 := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h1 : (1 : A) - u = 0 := by
    calc (1 : A) - u = (2 : ℂ) • (2 : ℂ)⁻¹ • (1 - u) :=
          (smul_inv_smul₀ h2 _).symm
      _ = 0 := by rw [h, smul_zero]
  exact (sub_eq_zero.mp h1).symm

end ScalarHelpers

section Reindex

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Reindexing unitaries preserves the operator-norm multiplicative defect. -/
theorem norm_unitaryReindexEquiv_sub_mul (e : m ≃ n)
    (a b c : Matrix.unitaryGroup m ℂ) :
    ‖((unitaryReindexEquiv e a : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) -
        ((unitaryReindexEquiv e b : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) *
          ((unitaryReindexEquiv e c : Matrix.unitaryGroup n ℂ) :
            Matrix n n ℂ)‖ =
      ‖(a : Matrix m m ℂ) - (b : Matrix m m ℂ) * (c : Matrix m m ℂ)‖ := by
  change ‖(matrixReindexStarAlgEquiv e) (a : Matrix m m ℂ) -
      (matrixReindexStarAlgEquiv e) (b : Matrix m m ℂ) *
        (matrixReindexStarAlgEquiv e) (c : Matrix m m ℂ)‖ =
    ‖(a : Matrix m m ℂ) - (b : Matrix m m ℂ) * (c : Matrix m m ℂ)‖
  rw [← map_mul (matrixReindexStarAlgEquiv e),
    ← map_sub (matrixReindexStarAlgEquiv e), norm_matrixReindexStarAlgEquiv]

/-- Reindexing unitaries preserves the operator-norm distance to `−1`. -/
theorem norm_unitaryReindexEquiv_add_one (e : m ≃ n)
    (a : Matrix.unitaryGroup m ℂ) :
    ‖((unitaryReindexEquiv e a : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) + 1‖ =
      ‖(a : Matrix m m ℂ) + 1‖ := by
  change ‖(matrixReindexStarAlgEquiv e) (a : Matrix m m ℂ) + 1‖ =
    ‖(a : Matrix m m ℂ) + 1‖
  rw [← map_one (matrixReindexStarAlgEquiv e),
    ← map_add (matrixReindexStarAlgEquiv e), norm_matrixReindexStarAlgEquiv]

end Reindex

/-- **The central involution becomes `−1` on a corner asymptotic
representation.** An injective corona representation of a countable group
with a nontrivial central involution `J` yields an operator-norm asymptotic
homomorphism into `U(d_k)`, `d_k > 0`, with `‖V_k(J) + 1‖_op → 0`. -/
theorem exists_opAsymptoticRep_of_injective_coronaRep
    (Γ : Type) [Group Γ] [Countable Γ]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : Γ →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hrho : Function.Injective rho) (J : Γ) (hJne : J ≠ 1)
    (hJJ : J * J = 1) (hJcent : ∀ g : Γ, g * J = J * g) :
    ∃ d : ℕ → ℕ, (∀ n, 0 < d n) ∧
      ∃ V : ∀ n, Γ → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ,
        (∀ g h : Γ, Tendsto (fun n ↦
          ‖(V n (g * h) : Matrix (naturalFiniteModel (d n))
              (naturalFiniteModel (d n)) ℂ) -
            (V n g : Matrix (naturalFiniteModel (d n))
              (naturalFiniteModel (d n)) ℂ) *
            (V n h : Matrix (naturalFiniteModel (d n))
              (naturalFiniteModel (d n)) ℂ)‖) atTop (𝓝 0)) ∧
        Tendsto (fun n ↦
          ‖(V n J : Matrix (naturalFiniteModel (d n))
              (naturalFiniteModel (d n)) ℂ) + 1‖) atTop (𝓝 0) := by
  -- Step 1: `u = ρ(J)` is a self-adjoint unitary and `q = ½(1 − u)` a
  -- projection.
  set u : NormMatrixCStarCorona (fun n ↦ X n) :=
    ((rho J : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
      NormMatrixCStarCorona (fun n ↦ X n))
  have hJ2 : rho J * rho J = 1 := by rw [← map_mul, hJJ, map_one]
  have huu : u * u = 1 := congrArg Subtype.val hJ2
  have hstar_mul : star u * u = 1 :=
    Unitary.star_mul_self_of_mem (rho J).prop
  have hustar : star u = u := by
    calc star u = star u * (u * u) := by rw [huu, mul_one]
      _ = star u * u * u := by rw [mul_assoc]
      _ = u := by rw [hstar_mul, one_mul]
  have hsa : star ((2 : ℂ)⁻¹ • (1 - u)) = (2 : ℂ)⁻¹ • (1 - u) := by
    rw [star_smul, star_sub, star_one, hustar, star_inv₀, star_ofNat]
  have hproj : ((2 : ℂ)⁻¹ • (1 - u)) * ((2 : ℂ)⁻¹ • (1 - u)) =
      (2 : ℂ)⁻¹ • (1 - u) :=
    bdl_half_one_sub_idempotent huu
  -- Step 2: `q ≠ 0`, by injectivity.
  have hqne : (2 : ℂ)⁻¹ • (1 - u) ≠ 0 := by
    intro h0
    apply hJne
    apply hrho
    apply Subtype.ext
    rw [map_one]
    exact bdl_eq_one_of_half_one_sub_eq_zero h0
  -- Step 3: `q` commutes with `ρ(Γ)`.
  have hcomm : ∀ g : Γ,
      ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * ((2 : ℂ)⁻¹ • (1 - u)) =
        ((2 : ℂ)⁻¹ • (1 - u)) *
          ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro g
    have h1 : rho g * rho J = rho J * rho g := by
      rw [← map_mul, ← map_mul, hJcent g]
    exact bdl_mul_half_one_sub_comm (congrArg Subtype.val h1)
  -- Step 4: the printed central corona corner.
  obtain ⟨φ, hφ, Q, r, _, W, amb, _, hQmk, _, hr, hJadd, _, _, hJnorm, hJone,
      _, _, _, hWdef, hamb, hambmk⟩ :=
    OneSidedMFRadical.CentralCoronaCornerPrintedRoute.manuscriptPrintedCentralCoronaCorner
      Γ X rho ((2 : ℂ)⁻¹ • (1 - u)) hsa hproj hqne hcomm
  -- Step 5: `q u = −q`, so `[amb J + restrict Q] = 0`.
  have hambJ : normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (amb J) =
      OneSidedMFRadical.coronaRestrict X φ hφ
        (((2 : ℂ)⁻¹ • (1 - u)) * u) :=
    hambmk J
  have hqu : ((2 : ℂ)⁻¹ • (1 - u)) * u = -((2 : ℂ)⁻¹ • (1 - u)) :=
    bdl_half_one_sub_mul_self huu
  rw [hqu, map_neg, ← hQmk, OneSidedMFRadical.coronaRestrict_mk] at hambJ
  have hzero : normMatrixCStarCoronaMk (fun k ↦ X (φ k))
      (amb J + OneSidedMFRadical.restrictSeq X φ Q) = 0 := by
    rw [map_add, hambJ, neg_add_cancel]
  have ht := (OneSidedMFRadical.normMatrixCStarCoronaMk_eq_zero_iff_tendsto
    (fun k ↦ X (φ k)) _).mp hzero
  have hWJ : Tendsto (fun k ↦
      ‖((W k J : Matrix.unitaryGroup (r k) ℂ) : Matrix (r k) (r k) ℂ) + 1‖)
      atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun k ↦ ?_) ht
    change ‖(amb J : ∀ k, Matrix (X (φ k)) (X (φ k)) ℂ) k +
        (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k)‖ = _
    rw [hamb J k, ← hJone k, ← hJadd k, hJnorm k]
  -- Step 6: reindex the corner models to natural dimensions.
  refine ⟨fun k ↦ Fintype.card (r k), hr,
    fun k g ↦ unitaryReindexEquiv (Fintype.equivFin (r k)) (W k g), ?_, ?_⟩
  · intro g h
    refine Filter.Tendsto.congr (fun k ↦ ?_) (hWdef g h)
    exact (norm_unitaryReindexEquiv_sub_mul (Fintype.equivFin (r k))
      (W k (g * h)) (W k g) (W k h)).symm
  · refine Filter.Tendsto.congr (fun k ↦ ?_) hWJ
    exact (norm_unitaryReindexEquiv_add_one (Fintype.equivFin (r k))
      (W k J)).symm

end

end RelatedBDL
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedBDL.exists_opAsymptoticRep_of_injective_coronaRep
