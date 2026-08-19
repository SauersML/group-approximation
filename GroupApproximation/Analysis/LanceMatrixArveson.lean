import GroupApproximation.Analysis.LanceChoiFunctional
import GroupApproximation.Analysis.LanceBlockOperator
import GroupApproximation.Analysis.LanceHermitianFunctional
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Arveson extension for matrix targets

Toward proof-ledger row `RE.05` (the Lance debt).  **The extension step**: a
unital map `Φ` from a closed star subalgebra `C` of a unital C⋆-algebra into
`B(ℂᵏ)`, completely positive in the form sense and commuting with the star,
extends to a unital completely positive map on the whole algebra.

The route is Choi's: the functional
`s(b) = ∑ pq ⟪e_p, Φ (b p q) e_q⟫` on matrices over `C`
(`Analysis/LanceChoiFunctional`) is nonnegative on ambient positives, so the
Krein theorem (`Analysis/StateExtension`) extends it to a positive functional
on all matrices; the extension is hermitian
(`Analysis/LanceHermitianFunctional`); the extended operator map is read off
from single-entry matrices through `Matrix.toEuclideanCLM`; and its complete
positivity is the one-nonzero-row computation

  `∑ ij ⟪v i, Ψ((star N * N)_{ij}) (v j)⟫ = s~(∑ r, star R_r * R_r) ≥ 0`,

fed to the block-operator bridge
(`Analysis/LanceBlockOperator.exists_factor_of_blockOp_form_nonneg`).

Equalities that cross the `Matrix`/`CStarMatrix` type synonym are produced as
terms and chained by `calc`, never rewritten: the two carry definitionally
equal but syntactically distinct instances, and `rw` cannot see across them.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

noncomputable section

variable {A : Type} [CStarAlgebra A]

/-! ## Euclidean helpers -/

theorem inner_single_toEuclideanCLM {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ)
    (p q : Fin k) :
    ⟪EuclideanSpace.single p (1 : ℂ),
      Matrix.toEuclideanCLM (𝕜 := ℂ) M
        (EuclideanSpace.single q (1 : ℂ))⟫_ℂ = M p q := by
  classical
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  have h0 := Matrix.ofLp_toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M
    (EuclideanSpace.single q (1 : ℂ))
  have h2 : Matrix.toEuclideanCLM (𝕜 := ℂ) M
      (EuclideanSpace.single q (1 : ℂ)) p
      = Matrix.mulVec M
          (WithLp.ofLp (EuclideanSpace.single q (1 : ℂ))) p :=
    congrArg (fun f : Fin k → ℂ ↦ f p) h0
  have h3 : WithLp.ofLp (EuclideanSpace.single q (1 : ℂ))
      = Pi.single q (1 : ℂ) := rfl
  rw [h2, h3]
  simp [Matrix.mulVec_single]

theorem inner_toEuclideanCLM_expand {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ)
    (u w : EuclideanSpace ℂ (Fin k)) :
    ⟪u, Matrix.toEuclideanCLM (𝕜 := ℂ) M w⟫_ℂ
      = ∑ p : Fin k, ∑ q : Fin k,
          (starRingEnd ℂ) (u p) * (M p q * w q) := by
  classical
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have happ : Matrix.toEuclideanCLM (𝕜 := ℂ) M w p
      = ∑ q : Fin k, M p q * w q := by
    have h0 := Matrix.ofLp_toEuclideanCLM (n := Fin k) (𝕜 := ℂ) M w
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ) M w p
        = Matrix.mulVec M (WithLp.ofLp w) p :=
      congrArg (fun f : Fin k → ℂ ↦ f p) h0
    rw [h1]
    simp [Matrix.mulVec, dotProduct]
  rw [RCLike.inner_apply', happ, Finset.mul_sum]

/-! ## The star of a single-entry matrix -/

theorem star_matrix_single {k : ℕ} (x : A) (p q : Fin k) :
    star (Matrix.single p q x) = Matrix.single q p (star x) := by
  classical
  funext p' q'
  show star ((Matrix.single p q x) q' p') = (Matrix.single q p (star x)) p' q'
  rw [Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : p = q' <;> by_cases h2 : q = p' <;>
    simp [h1, h2, and_comm, star_zero]

/-- The single-entry embedding `A → CStarMatrix` as a linear map. -/
def singleEntryLM (k : ℕ) (p q : Fin k) :
    A →ₗ[ℂ] CStarMatrix (Fin k) (Fin k) A where
  toFun x := (Matrix.single p q x : CStarMatrix (Fin k) (Fin k) A)
  map_add' x y := Matrix.single_add p q x y
  map_smul' z x := (Matrix.smul_single z p q x).symm

/-! ## The extension theorem -/

variable [PartialOrder A] [StarOrderedRing A]

/-- **Arveson extension for matrix targets.**  A unital map from a closed
star subalgebra into `B(ℂᵏ)` that is completely positive in the form sense
and commutes with the star extends to a unital completely positive map on
the whole algebra. -/
theorem exists_ucp_extension (C : StarSubalgebra ℂ A)
    (hC : IsClosed (C : Set A)) {k : ℕ}
    (Φ : ↥C →ₗ[ℂ] (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))
    (hform : ∀ (m : ℕ) (a : Fin m → ↥C)
      (v : Fin m → EuclideanSpace ℂ (Fin k)),
      0 ≤ (∑ i : Fin m, ∑ j : Fin m,
        ⟪v i, Φ (star (a i) * a j) (v j)⟫_ℂ).re)
    (hstar : ∀ c : ↥C, Φ (star c) = star (Φ c))
    (hone : Φ 1 = 1) :
    ∃ Ψ : A →ₗ[ℂ] (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)),
      IsCompletelyPositive Ψ ∧ Ψ 1 = 1 ∧
        ∀ c : ↥C, Ψ (c : A) = Φ c := by
  classical
  obtain ⟨sExt, hext, hpos⟩ :=
    StateExtension.exists_positive_extension
      (B := matrixStarSubalgebra C k) (φ := choiFunctional C Φ)
      (fun b hb ↦ choiFunctional_nonneg C Φ hC hform hstar b hb)
  have hherm : ∀ y : CStarMatrix (Fin k) (Fin k) A,
      sExt (star y) = (starRingEnd ℂ) (sExt y) :=
    StateExtension.hermitian_of_nonneg sExt hpos
  -- the single-entry values of the extension, as linear functionals on `A`
  set sEL : Fin k → Fin k → (A →ₗ[ℂ] ℂ) := fun p q ↦
    sExt ∘ₗ singleEntryLM (A := A) k p q with hsEL_def
  have hsEL_apply : ∀ (p q : Fin k) (x : A), sEL p q x
      = sExt ((Matrix.single p q x : CStarMatrix (Fin k) (Fin k) A)) := by
    intro p q x
    rw [hsEL_def]
    rfl
  -- the reconstructed matrix of entry values
  set Ψmat : A → Matrix (Fin k) (Fin k) ℂ := fun x ↦
    Matrix.of fun p q ↦ sEL p q x with hΨmat_def
  have hΨmat_apply : ∀ (x : A) (p q : Fin k), Ψmat x p q = sEL p q x := by
    intro x p q
    rw [hΨmat_def]
    rfl
  have hΨmat_add : ∀ x y : A, Ψmat (x + y) = Ψmat x + Ψmat y := by
    intro x y
    funext p q
    rw [hΨmat_def]
    exact (sEL p q).map_add x y
  have hΨmat_smul : ∀ (z : ℂ) (x : A), Ψmat (z • x) = z • Ψmat x := by
    intro z x
    funext p q
    rw [hΨmat_def]
    exact (sEL p q).map_smul z x
  -- the reconstructed map
  set Ψ : A →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :=
    { toFun := fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (Ψmat x)
      map_add' := fun x y ↦ by rw [hΨmat_add, map_add]
      map_smul' := fun z x ↦ by
        rw [hΨmat_smul, map_smul, RingHom.id_apply] } with hΨ_def
  have hΨ_apply : ∀ x : A, Ψ x = Matrix.toEuclideanCLM (𝕜 := ℂ) (Ψmat x) := by
    intro x
    rw [hΨ_def]
    rfl
  -- extension property
  have hextend : ∀ c : ↥C, Ψ (c : A) = Φ c := by
    intro c
    rw [hΨ_apply]
    have hmat : Ψmat (c : A)
        = (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (Φ c) := by
      funext p q
      have h2 := inner_single_toEuclideanCLM
        ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (Φ c)) p q
      rw [StarAlgEquiv.apply_symm_apply] at h2
      calc Ψmat (c : A) p q
          = sEL p q (c : A) := hΨmat_apply _ p q
        _ = sExt ((Matrix.single p q ((c : A)) :
              CStarMatrix (Fin k) (Fin k) A)) := hsEL_apply p q _
        _ = choiFunctional C Φ
              ⟨(Matrix.single p q ((c : A)) :
                  CStarMatrix (Fin k) (Fin k) A),
                single_mem_matrixStarSubalgebra C c p q⟩ :=
            hext ⟨_, single_mem_matrixStarSubalgebra C c p q⟩
        _ = ⟪EuclideanSpace.single p (1 : ℂ),
              Φ c (EuclideanSpace.single q (1 : ℂ))⟫_ℂ :=
            choiFunctional_single C Φ c p q
        _ = (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (Φ c) p q := h2
    rw [hmat, StarAlgEquiv.apply_symm_apply]
  -- unitality
  have hunit : Ψ 1 = 1 := by
    have h1 : (1 : A) ∈ C := C.one_mem
    have h2 := hextend ⟨1, h1⟩
    have hc : ((⟨1, h1⟩ : ↥C) : A) = (1 : A) := rfl
    rw [hc] at h2
    rw [h2, show (⟨1, h1⟩ : ↥C) = 1 from rfl, hone]
  -- the star is preserved
  have hΨstar : ∀ x : A, star (Ψ x) = Ψ (star x) := by
    intro x
    rw [hΨ_apply, hΨ_apply, ← map_star]
    congr 1
    funext p q
    calc star (Ψmat x) p q
        = (starRingEnd ℂ) (Ψmat x q p) := Matrix.star_apply _ _ _
      _ = (starRingEnd ℂ) (sEL q p x) := by rw [hΨmat_apply]
      _ = (starRingEnd ℂ) (sExt ((Matrix.single q p x :
            CStarMatrix (Fin k) (Fin k) A))) := by rw [hsEL_apply]
      _ = sExt (star ((Matrix.single q p x :
            CStarMatrix (Fin k) (Fin k) A))) := (hherm _).symm
      _ = sExt ((Matrix.single p q (star x) :
            CStarMatrix (Fin k) (Fin k) A)) :=
          congrArg sExt (star_matrix_single x q p)
      _ = sEL p q (star x) := (hsEL_apply p q _).symm
      _ = Ψmat (star x) p q := (hΨmat_apply _ p q).symm
  -- complete positivity
  refine ⟨Ψ, ?_, hunit, hextend⟩
  intro m M hM
  obtain ⟨N, hN⟩ := hM
  have hMsa : star M = M := by
    rw [hN, star_mul, star_star]
  have hMentry : ∀ i j : Fin m, M i j
      = ∑ r : Fin m, star (N r i) * N r j := by
    intro i j
    calc M i j = (star N * N) i j :=
          congrArg (fun T : CStarMatrix (Fin m) (Fin m) A ↦ T i j) hN
      _ = ∑ r : Fin m, (star N) i r * N r j := Matrix.mul_apply
      _ = ∑ r : Fin m, star (N r i) * N r j :=
          Finset.sum_congr rfl fun r _ ↦ rfl
  have hXsa : star (M.map ⇑Ψ) = M.map ⇑Ψ := by
    funext i j
    calc star (M.map ⇑Ψ) i j
        = star ((M.map ⇑Ψ) j i) := Matrix.star_apply _ _ _
      _ = star (Ψ (M j i)) := rfl
      _ = Ψ (star (M j i)) := hΨstar _
      _ = Ψ ((star M) i j) := rfl
      _ = Ψ (M i j) := by rw [hMsa]
      _ = (M.map ⇑Ψ) i j := rfl
  have hformX : ∀ v : PiLp 2 (fun _ : Fin m ↦ EuclideanSpace ℂ (Fin k)),
      0 ≤ (⟪v, blockOp (M.map ⇑Ψ) v⟫_ℂ).re := by
    intro v
    rw [inner_blockOp]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · have hzero : ∀ i j : Fin m,
          ⟪v i, (M.map ⇑Ψ) i j (v j)⟫_ℂ = 0 := by
        intro i j
        have hvi : v i = 0 := by
          ext z
          exact absurd (hk ▸ z.2) (Nat.not_lt_zero z.1)
        rw [hvi, inner_zero_left]
      rw [Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ hzero i j]
      simp
    · set p0 : Fin k := ⟨0, hk⟩ with hp0_def
      set d : Fin m → Fin k → A := fun r s ↦
        ∑ i : Fin m, ((v i) s) • N r i with hd_def
      have hd_apply : ∀ r s, d r s = ∑ i : Fin m, ((v i) s) • N r i := by
        intro r s
        rw [hd_def]
      set R : Fin m → CStarMatrix (Fin k) (Fin k) A := fun r ↦
        ((Matrix.of fun p q ↦ if p = p0 then d r q else 0 :
          Matrix (Fin k) (Fin k) A) : CStarMatrix (Fin k) (Fin k) A)
        with hR_def
      have hR_apply : ∀ r p q, R r p q = if p = p0 then d r q else 0 := by
        intro r p q
        rw [hR_def]
        rfl
      have hRentry_same : ∀ r q, R r p0 q = d r q := by
        intro r q
        rw [hR_apply r p0 q, if_pos rfl]
      have hRentry_ne : ∀ r t q, t ≠ p0 → R r t q = 0 := by
        intro r t q ht
        rw [hR_apply r t q, if_neg ht]
      have hRR : ∀ (r : Fin m) (p q : Fin k),
          (star (R r) * R r) p q = star (d r p) * d r q := by
        intro r p q
        calc (star (R r) * R r) p q
            = ∑ t : Fin k, (star (R r)) p t * R r t q := Matrix.mul_apply
          _ = (star (R r)) p p0 * R r p0 q := by
              refine Finset.sum_eq_single p0 (fun t _ ht ↦ ?_)
                (fun h ↦ absurd (Finset.mem_univ p0) h)
              rw [hRentry_ne r t q ht, mul_zero]
          _ = star (d r p) * d r q := by
              have h1 : (star (R r)) p p0 = star (R r p0 p) :=
                Matrix.star_apply _ _ _
              rw [h1, hRentry_same r p, hRentry_same r q]
      have hd_star : ∀ r p, star (d r p)
          = ∑ i : Fin m, (starRingEnd ℂ) ((v i) p) • star (N r i) := by
        intro r p
        rw [hd_apply r p, star_sum]
        exact Finset.sum_congr rfl fun i _ ↦ star_smul _ _
      have hd2 : ∀ (r : Fin m) (p q : Fin k), star (d r p) * d r q
          = ∑ i : Fin m, ∑ j : Fin m,
              (((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                (star (N r i) * N r j) : A) := by
        intro r p q
        rw [hd_star r p, hd_apply r q, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ smul_mul_smul_comm _ _ _ _
      -- each term of the block form through the functional
      have hterm : ∀ i j : Fin m,
          ⟪v i, (M.map ⇑Ψ) i j (v j)⟫_ℂ
          = ∑ p : Fin k, ∑ q : Fin k,
              sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                M i j : A)) := by
        intro i j
        have h0 : (M.map ⇑Ψ) i j
            = Matrix.toEuclideanCLM (𝕜 := ℂ) (Ψmat (M i j)) := by
          have h1 : (M.map ⇑Ψ) i j = Ψ (M i j) := rfl
          rw [h1, hΨ_apply]
        rw [h0, inner_toEuclideanCLM_expand]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        calc (starRingEnd ℂ) ((v i) p) * (Ψmat (M i j) p q * ((v j) q))
            = ((starRingEnd ℂ) ((v i) p) * ((v j) q)) * sEL p q (M i j) := by
              rw [hΨmat_apply]
              ring
          _ = sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                M i j : A)) := ((sEL p q).map_smul _ _).symm
      -- reorder the four sums
      have hswap : (∑ i : Fin m, ∑ j : Fin m, ∑ p : Fin k, ∑ q : Fin k,
            sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
              M i j : A)))
          = ∑ p : Fin k, ∑ q : Fin k, ∑ i : Fin m, ∑ j : Fin m,
              sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                M i j : A)) :=
        calc (∑ i : Fin m, ∑ j : Fin m, ∑ p : Fin k, ∑ q : Fin k,
              sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                M i j : A)))
            = ∑ i : Fin m, ∑ p : Fin k, ∑ j : Fin m, ∑ q : Fin k,
                sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                  M i j : A)) :=
              Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
          _ = ∑ p : Fin k, ∑ i : Fin m, ∑ j : Fin m, ∑ q : Fin k,
                sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                  M i j : A)) := Finset.sum_comm
          _ = ∑ p : Fin k, ∑ i : Fin m, ∑ q : Fin k, ∑ j : Fin m,
                sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                  M i j : A)) :=
              Finset.sum_congr rfl fun p _ ↦
                Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
          _ = ∑ p : Fin k, ∑ q : Fin k, ∑ i : Fin m, ∑ j : Fin m,
                sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                  M i j : A)) :=
              Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm
      -- pull the sums inside the functional
      have hlin : ∀ p q : Fin k,
          (∑ i : Fin m, ∑ j : Fin m,
            sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
              M i j : A)))
          = sEL p q (∑ i : Fin m, ∑ j : Fin m,
              (((starRingEnd ℂ) ((v i) p) * ((v j) q)) • M i j : A)) := by
        intro p q
        calc (∑ i : Fin m, ∑ j : Fin m,
              sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                M i j : A)))
            = ∑ i : Fin m, sEL p q (∑ j : Fin m,
                (((starRingEnd ℂ) ((v i) p) * ((v j) q)) • M i j : A)) :=
              Finset.sum_congr rfl fun i _ ↦ (map_sum (sEL p q) _ _).symm
          _ = sEL p q (∑ i : Fin m, ∑ j : Fin m,
                (((starRingEnd ℂ) ((v i) p) * ((v j) q)) • M i j : A)) :=
              (map_sum (sEL p q) _ _).symm
      -- identify the inner sums with the entries of the sum of squares
      have hinner : ∀ p q : Fin k,
          (∑ i : Fin m, ∑ j : Fin m,
            (((starRingEnd ℂ) ((v i) p) * ((v j) q)) • M i j : A))
          = (∑ r : Fin m, star (R r) * R r) p q := by
        intro p q
        have hRHS1 : (∑ r : Fin m, star (R r) * R r) p
            = ∑ r : Fin m, (star (R r) * R r) p :=
          Finset.sum_apply p Finset.univ _
        have hRHS : (∑ r : Fin m, star (R r) * R r) p q
            = ∑ r : Fin m, (star (R r) * R r) p q :=
          (congrArg (fun f ↦ f q) hRHS1).trans
            (Finset.sum_apply q Finset.univ _)
        calc (∑ i : Fin m, ∑ j : Fin m,
              (((starRingEnd ℂ) ((v i) p) * ((v j) q)) • M i j : A))
            = ∑ i : Fin m, ∑ j : Fin m, ∑ r : Fin m,
                (((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                  (star (N r i) * N r j) : A) := by
              refine Finset.sum_congr rfl fun i _ ↦
                Finset.sum_congr rfl fun j _ ↦ ?_
              rw [hMentry i j, Finset.smul_sum]
          _ = ∑ i : Fin m, ∑ r : Fin m, ∑ j : Fin m,
                (((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                  (star (N r i) * N r j) : A) :=
              Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
          _ = ∑ r : Fin m, ∑ i : Fin m, ∑ j : Fin m,
                (((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                  (star (N r i) * N r j) : A) := Finset.sum_comm
          _ = ∑ r : Fin m, star (d r p) * d r q :=
              Finset.sum_congr rfl fun r _ ↦ (hd2 r p q).symm
          _ = ∑ r : Fin m, (star (R r) * R r) p q :=
              Finset.sum_congr rfl fun r _ ↦ (hRR r p q).symm
          _ = (∑ r : Fin m, star (R r) * R r) p q := hRHS.symm
      -- the value is the functional at the sum of squares
      have hcollect : (∑ p : Fin k, ∑ q : Fin k,
            sEL p q ((∑ r : Fin m, star (R r) * R r) p q))
          = sExt (∑ r : Fin m, star (R r) * R r) := by
        have hW0 : (∑ r : Fin m, star (R r) * R r)
            = ∑ p : Fin k, ∑ q : Fin k,
                ((Matrix.single p q
                    ((∑ r : Fin m, star (R r) * R r) p q) :
                  CStarMatrix (Fin k) (Fin k) A)) :=
          Matrix.matrix_eq_sum_single _
        calc (∑ p : Fin k, ∑ q : Fin k,
              sEL p q ((∑ r : Fin m, star (R r) * R r) p q))
            = ∑ p : Fin k, ∑ q : Fin k,
                sExt ((Matrix.single p q
                    ((∑ r : Fin m, star (R r) * R r) p q) :
                  CStarMatrix (Fin k) (Fin k) A)) :=
              Finset.sum_congr rfl fun p _ ↦
                Finset.sum_congr rfl fun q _ ↦ hsEL_apply p q _
          _ = ∑ p : Fin k, sExt (∑ q : Fin k,
                ((Matrix.single p q
                    ((∑ r : Fin m, star (R r) * R r) p q) :
                  CStarMatrix (Fin k) (Fin k) A))) :=
              Finset.sum_congr rfl fun p _ ↦ (map_sum sExt _ _).symm
          _ = sExt (∑ p : Fin k, ∑ q : Fin k,
                ((Matrix.single p q
                    ((∑ r : Fin m, star (R r) * R r) p q) :
                  CStarMatrix (Fin k) (Fin k) A))) :=
              (map_sum sExt _ _).symm
          _ = sExt (∑ r : Fin m, star (R r) * R r) :=
              (congrArg sExt hW0).symm
      -- assemble
      have hchain : (∑ i : Fin m, ∑ j : Fin m,
            ⟪v i, (M.map ⇑Ψ) i j (v j)⟫_ℂ)
          = sExt (∑ r : Fin m, star (R r) * R r) :=
        calc (∑ i : Fin m, ∑ j : Fin m, ⟪v i, (M.map ⇑Ψ) i j (v j)⟫_ℂ)
            = ∑ i : Fin m, ∑ j : Fin m, ∑ p : Fin k, ∑ q : Fin k,
                sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                  M i j : A)) :=
              Finset.sum_congr rfl fun i _ ↦
                Finset.sum_congr rfl fun j _ ↦ hterm i j
          _ = ∑ p : Fin k, ∑ q : Fin k, ∑ i : Fin m, ∑ j : Fin m,
                sEL p q ((((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                  M i j : A)) := hswap
          _ = ∑ p : Fin k, ∑ q : Fin k,
                sEL p q (∑ i : Fin m, ∑ j : Fin m,
                  (((starRingEnd ℂ) ((v i) p) * ((v j) q)) •
                    M i j : A)) :=
              Finset.sum_congr rfl fun p _ ↦
                Finset.sum_congr rfl fun q _ ↦ hlin p q
          _ = ∑ p : Fin k, ∑ q : Fin k,
                sEL p q ((∑ r : Fin m, star (R r) * R r) p q) :=
              Finset.sum_congr rfl fun p _ ↦
                Finset.sum_congr rfl fun q _ ↦
                  congrArg (sEL p q) (hinner p q)
          _ = sExt (∑ r : Fin m, star (R r) * R r) := hcollect
      have hWpos : (0 : CStarMatrix (Fin k) (Fin k) A)
          ≤ ∑ r : Fin m, star (R r) * R r :=
        Finset.sum_nonneg fun r _ ↦ star_mul_self_nonneg (R r)
      obtain ⟨t, ht0, htv⟩ := hpos _ hWpos
      rw [hchain, htv]
      simpa using ht0
  obtain ⟨P, hP⟩ := exists_factor_of_blockOp_form_nonneg hXsa hformX
  exact ⟨P, hP⟩

end

end CStarExactness
end GroupApproximation
