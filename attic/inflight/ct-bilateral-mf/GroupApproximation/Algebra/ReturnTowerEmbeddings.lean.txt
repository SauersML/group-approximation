import GroupApproximation.Algebra.ReturnTowerUnits
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Return towers: the embedding clauses over an identified return ring

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1723–1741:

> $P_C=\operatorname{LC}(C,k)\rtimes_{S_C}\mathbb Z$ [...] Thus $R_X$ is a unital
> corner of $M_{2r-1}(P_C)$, via $x\mapsto(b_i x a_j)_{ij}$. [...]
> Unitization embeds $\GL_{nr}(P_C)$ into $\GL_n(R_X)$.
> For $n\ge2$, block elementary flattening puts the image of
> $\EL_{nr}(P_C)$ inside $\EL_n(R_X)$.

`Algebra/ReturnTowerUnits` proves these for the corner ring `τ.Base = p R p` of a return tower
`τ`.  The corollary's assembly (`DynamicRankBudget.ReturnEmbeddingStatement`) states them over
the crossed product of the first-return system, so this module transports them along a ring
isomorphism `θ : A ≃+* τ.Base`; at `R_X` this is the identification of
`ReturnRingCrossedProductStatement` (tex 1723–1726), whose target is `τ.Base` for
`returnTowerUnits` (`returnTowerUnits_p` is `rfl`).

* `matrixEmbedding τ θ : R →ₙ+* M_N(A)`, `x ↦ (θ⁻¹(b_i x a_j))_{ij}`, injective;
* `blockTransport τ θ n : GL_{n·r}(A) ≃* GL_n(M_r(P_C))`: coefficients along `θ`,
  `Fin (n·r) ≃ Fin n × Fin r` along `finProdFinEquiv`, then block unflattening
  (`coe_blockTransport_apply`);
* `glEmbedding τ θ n = unitizeGL ∘ blockTransport`, injective;
* `glEmbedding_mem_elementaryGroup`, `elEmbedding τ θ n hn : EL_{n·r}(A) →* EL_n(R)` (`n ≥ 2`),
  `coe_elEmbedding`, injective;
* `unitEmbedding τ θ : GL_r(A) →* Rˣ`, the case `n = 1` read in the `1 × 1` entry
  (`unitEmbedding_apply`), injective;
* `returnEmbeddingClauses`: the four injective clauses of `ReturnEmbeddingStatement`, and
  `returnEmbeddingClauses_of_corner` with `θ` into the corner of an idempotent `p = τ.p`.
-/

namespace GroupApproximation.ChainCore

open MFQuotientUnits

/-- The entry of a `1 × 1` matrix, as a monoid homomorphism. -/
def matrixFinOneEntry (R : Type*) [Ring R] : Matrix (Fin 1) (Fin 1) R →* R where
  toFun M := M 0 0
  map_one' := by simp
  map_mul' M M' := by
    show (M * M') 0 0 = M 0 0 * M' 0 0
    rw [Matrix.mul_apply, Fin.sum_univ_one]

theorem matrixFinOneEntry_injective (R : Type*) [Ring R] :
    Function.Injective (matrixFinOneEntry R) := fun M M' h =>
  Matrix.ext fun i j => by
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact h

namespace ReturnTowerUnits

variable {R A : Type*} [Ring R] [Ring A] {N r : ℕ}

/-- **`R_X` is a corner of `M_{2r-1}(P_C)`** (tex 1732–1733), with `P_C` identified with `A`:
`x ↦ (θ⁻¹(b_i x a_j))_{ij}`. -/
def matrixEmbedding (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) :
    R →ₙ+* Matrix (Fin N) (Fin N) A :=
  (θ.symm.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) τ.Base →+* Matrix (Fin N) (Fin N) A)
    |>.toNonUnitalRingHom.comp τ.toMatrix

theorem matrixEmbedding_injective (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) :
    Function.Injective (τ.matrixEmbedding θ) := fun _ _ h =>
  τ.toMatrix_injective (Matrix.map_injective θ.symm.injective h)

/-- **The coefficient and index transport** `GL_{n·r}(A) ≃ GL_n(M_r(P_C))`: coefficients along
`θ`, `Fin (n·r) ≃ Fin n × Fin r` along `finProdFinEquiv`, then block unflattening. -/
def blockTransport (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) (n : ℕ) :
    (Matrix (Fin (n * r)) (Fin (n * r)) A)ˣ ≃*
      (Matrix (Fin n) (Fin n) (Matrix (Fin r) (Fin r) τ.Base))ˣ :=
  ((Units.mapEquiv (θ.mapMatrix (m := Fin (n * r))).toMulEquiv).trans
      (elementaryReindexUnitEquiv (R := τ.Base) (finProdFinEquiv (m := n) (n := r)).symm)).trans
    (elementaryBlockUnitEquiv (ι := Fin n) (κ := Fin r) (R := τ.Base)).symm

/-- The entries of `blockTransport`: `(i, j)` block, `(a, b)` entry, read at
`(finProdFinEquiv (i, a), finProdFinEquiv (j, b))`. -/
theorem coe_blockTransport_apply (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) (n : ℕ)
    (y : (Matrix (Fin (n * r)) (Fin (n * r)) A)ˣ) (i j : Fin n) (a b : Fin r) :
    (((τ.blockTransport θ n y : Matrix (Fin n) (Fin n) (Matrix (Fin r) (Fin r) τ.Base))
        i j a b : τ.Base) : R) =
      (θ ((y : Matrix (Fin (n * r)) (Fin (n * r)) A) (finProdFinEquiv (i, a))
        (finProdFinEquiv (j, b))) : R) :=
  rfl

/-- **Unitization embeds `GL_{nr}(P_C)` into `GL_n(R_X)`** (tex 1739), with `P_C` identified with
`A` and `Fin (n·r)` with `Fin n × Fin r`. -/
def glEmbedding (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) (n : ℕ) :
    (Matrix (Fin (n * r)) (Fin (n * r)) A)ˣ →* (Matrix (Fin n) (Fin n) R)ˣ :=
  (τ.unitizeGL (Fin n)).comp (τ.blockTransport θ n).toMonoidHom

theorem glEmbedding_eq (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) (n : ℕ) :
    τ.glEmbedding θ n = (τ.unitizeGL (Fin n)).comp (τ.blockTransport θ n).toMonoidHom :=
  rfl

theorem glEmbedding_injective (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) (n : ℕ) :
    Function.Injective (τ.glEmbedding θ n) :=
  (τ.unitizeGL_injective (Fin n)).comp (τ.blockTransport θ n).injective

/-- **Block elementary flattening puts the image of `EL_{nr}(P_C)` inside `EL_n(R_X)`**
(tex 1740–1741), for `n ≥ 2`. -/
theorem glEmbedding_mem_elementaryGroup (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base)
    {n : ℕ} (hn : 2 ≤ n) {g : (Matrix (Fin (n * r)) (Fin (n * r)) A)ˣ}
    (hg : g ∈ elementaryGroup (Fin (n * r)) A) :
    τ.glEmbedding θ n g ∈ elementaryGroup (Fin n) R := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hmap : (Units.mapEquiv (θ.mapMatrix (m := Fin (n * r))).toMulEquiv).toMonoidHom =
      elementaryMatrixUnitMap (ι := Fin (n * r)) θ.toRingHom := by
    ext u
    rfl
  have h1 : (Units.mapEquiv (θ.mapMatrix (m := Fin (n * r))).toMulEquiv).toMonoidHom g ∈
      elementaryGroup (Fin (n * r)) τ.Base := by
    rw [hmap]
    exact elementaryGroup_map_le (ι := Fin (n * r)) θ.toRingHom
      (Subgroup.mem_map_of_mem (elementaryMatrixUnitMap (ι := Fin (n * r)) θ.toRingHom) hg)
  have h2 : (elementaryReindexUnitEquiv (R := τ.Base)
      (finProdFinEquiv (m := n) (n := r)).symm).toMonoidHom
        ((Units.mapEquiv (θ.mapMatrix (m := Fin (n * r))).toMulEquiv).toMonoidHom g) ∈
        elementaryGroup (Fin n × Fin r) τ.Base := by
    rw [← elementaryReindexGroup_map (R := τ.Base) (finProdFinEquiv (m := n) (n := r)).symm]
    exact Subgroup.mem_map_of_mem
      (elementaryReindexUnitEquiv (R := τ.Base) (finProdFinEquiv (m := n) (n := r)).symm).toMonoidHom
      h1
  exact τ.map_flat_elementaryGroup_le (Fin n)
    (Subgroup.mem_map_of_mem (τ.flatUnitizeGL (Fin n)) h2)

/-- **`EL_{nr}(P_C) → EL_n(R_X)`** (tex 1740–1741), `n ≥ 2`, with `P_C` identified with `A`. -/
def elEmbedding (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) (n : ℕ) (hn : 2 ≤ n) :
    ↥(elementaryGroup (Fin (n * r)) A) →* ↥(elementaryGroup (Fin n) R) :=
  ((τ.glEmbedding θ n).comp (elementaryGroup (Fin (n * r)) A).subtype).codRestrict
    (elementaryGroup (Fin n) R) fun g => τ.glEmbedding_mem_elementaryGroup θ hn g.2

theorem coe_elEmbedding (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) (n : ℕ) (hn : 2 ≤ n)
    (y : ↥(elementaryGroup (Fin (n * r)) A)) :
    ((τ.elEmbedding θ n hn y : ↥(elementaryGroup (Fin n) R)) : (Matrix (Fin n) (Fin n) R)ˣ) =
      τ.glEmbedding θ n (y : (Matrix (Fin (n * r)) (Fin (n * r)) A)ˣ) :=
  rfl

theorem elEmbedding_injective (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) (n : ℕ)
    (hn : 2 ≤ n) : Function.Injective (τ.elEmbedding θ n hn) := fun _ _ e =>
  Subtype.ext (τ.glEmbedding_injective θ n (congrArg Subtype.val e))

/-- **Unitization embeds `GL_r(P_C)` into `R_X^×`** (tex 1739 at `n = 1`), with `P_C` identified
with `A`. -/
def unitEmbedding (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) :
    (Matrix (Fin r) (Fin r) A)ˣ →* Rˣ :=
  (Units.map (matrixFinOneEntry R)).comp
    ((τ.glEmbedding θ 1).comp
      (elementaryReindexUnitEquiv (R := A) (finCongr (Nat.one_mul r).symm)).toMonoidHom)

theorem unitEmbedding_apply (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base)
    (y : (Matrix (Fin r) (Fin r) A)ˣ) :
    τ.unitEmbedding θ y = Units.map (matrixFinOneEntry R)
      (τ.glEmbedding θ 1 (elementaryReindexUnitEquiv (R := A) (finCongr (Nat.one_mul r).symm) y)) :=
  rfl

theorem unitEmbedding_injective (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) :
    Function.Injective (τ.unitEmbedding θ) :=
  (Units.map_injective (matrixFinOneEntry_injective R)).comp
    ((τ.glEmbedding_injective θ 1).comp
      (elementaryReindexUnitEquiv (R := A) (finCongr (Nat.one_mul r).symm)).injective)

/-- **The four injective embedding clauses** of `DynamicRankBudget.ReturnEmbeddingStatement`
(tex 1732–1741), for a return tower whose corner ring is identified with `A`. -/
theorem returnEmbeddingClauses (τ : ReturnTowerUnits R N r) (θ : A ≃+* τ.Base) :
    (∃ (m : ℕ) (ψ : R →ₙ+* Matrix (Fin m) (Fin m) A), Function.Injective ψ) ∧
      (∀ n : ℕ, 1 ≤ n → ∃ E : (Matrix (Fin (n * r)) (Fin (n * r)) A)ˣ →*
          (Matrix (Fin n) (Fin n) R)ˣ, Function.Injective E) ∧
      (∀ n : ℕ, 2 ≤ n → ∃ E : ↥(elementaryGroup (Fin (n * r)) A) →*
          ↥(elementaryGroup (Fin n) R), Function.Injective E) ∧
      (∃ E : (Matrix (Fin r) (Fin r) A)ˣ →* Rˣ, Function.Injective E) :=
  ⟨⟨N, τ.matrixEmbedding θ, τ.matrixEmbedding_injective θ⟩,
    fun n _ => ⟨τ.glEmbedding θ n, τ.glEmbedding_injective θ n⟩,
    fun n hn => ⟨τ.elEmbedding θ n hn, τ.elEmbedding_injective θ n hn⟩,
    ⟨τ.unitEmbedding θ, τ.unitEmbedding_injective θ⟩⟩

/-- `returnEmbeddingClauses` with the identification into the corner of an idempotent `p` equal to
`τ.p`, the shape of `ReturnRingCrossedProductStatement`. -/
theorem returnEmbeddingClauses_of_corner (τ : ReturnTowerUnits R N r) {p : R}
    {hp : IsIdempotentElem p} (θ : A ≃+* Corner R p hp) (hτp : τ.p = p) :
    (∃ (m : ℕ) (ψ : R →ₙ+* Matrix (Fin m) (Fin m) A), Function.Injective ψ) ∧
      (∀ n : ℕ, 1 ≤ n → ∃ E : (Matrix (Fin (n * r)) (Fin (n * r)) A)ˣ →*
          (Matrix (Fin n) (Fin n) R)ˣ, Function.Injective E) ∧
      (∀ n : ℕ, 2 ≤ n → ∃ E : ↥(elementaryGroup (Fin (n * r)) A) →*
          ↥(elementaryGroup (Fin n) R), Function.Injective E) ∧
      (∃ E : (Matrix (Fin r) (Fin r) A)ˣ →* Rˣ, Function.Injective E) := by
  subst hτp
  exact τ.returnEmbeddingClauses θ

end ReturnTowerUnits

end GroupApproximation.ChainCore

open GroupApproximation.ChainCore

#audit_axioms ReturnTowerUnits.matrixEmbedding_injective
#audit_axioms ReturnTowerUnits.coe_blockTransport_apply
#audit_axioms ReturnTowerUnits.glEmbedding_injective
#audit_axioms ReturnTowerUnits.elEmbedding_injective
#audit_axioms ReturnTowerUnits.unitEmbedding_injective
#audit_axioms ReturnTowerUnits.returnEmbeddingClauses
#audit_axioms ReturnTowerUnits.returnEmbeddingClauses_of_corner
