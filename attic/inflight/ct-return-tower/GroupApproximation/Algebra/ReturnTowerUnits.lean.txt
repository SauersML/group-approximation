import Mathlib.Data.Matrix.Composition
import GroupApproximation.Algebra.DirectlyFiniteCorner
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Return towers: the tower corner, the first levels, and unitization

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1727–1741:

> For $0\le i<2r-1$ put
> $D_i=\bigcup_{h>i}C_h$, $a_i=u^i1_{D_i}$, $b_i=1_{D_i}u^{-i}$.
> The tower partition gives $b_i a_j=0$ for $i\ne j$,
> $b_i a_i=1_{D_i}$ and $\sum_i a_i b_i=1$.  Thus $R_X$ is a unital
> corner of $M_{2r-1}(P_C)$, via $x\mapsto(b_i x a_j)_{ij}$.
> For $i<r$ we have $D_i=C$, so the first $r$ levels give the injection
> $\Phi\colon M_r(P_C)\to R_X$, $\Phi(A)=\sum_{i,j<r}a_i A_{ij}b_j$.
> Unitization embeds $\GL_{nr}(P_C)$ into $\GL_n(R_X)$.
> For $n\ge2$, block elementary flattening puts the image of
> $\EL_{nr}(P_C)$ inside $\EL_n(R_X)$.

Everything after "The tower partition gives" uses only the displayed identities, so this module
proves it for an arbitrary ring `R` carrying a `ReturnTowerUnits` system: levels `a i, b i`
(`i : Fin N`, printed `N = 2r-1`) with `b i * a j = 0` for `i ≠ j`, `∑ i, a i * b i = 1`,
`a i * p = a i`, `p * b i = b i` for the base idempotent `p` (printed `p_C = 1_C`), and
`b i * a i = p` for `i < r` (printed `D_i = C`).  The dynamical construction of such a system
in `R_X` is `ReturnTowerUnitsStatement` (`Dynamics/ReturnTowerStatements`).

* `ReturnTowerUnits.toMatrix : R →ₙ+* M_N(P_C)`, `x ↦ (b_i x a_j)_{ij}`, and
  `ReturnTowerUnits.cornerEquiv : R ≃+* E M_N(P_C) E` with `E = toMatrix 1`: `R` is a unital
  corner of `M_N(P_C)`.  Consequence: `ReturnTowerUnits.isDedekindFiniteMonoid`.
* `ReturnTowerUnits.phi : M_r(P_C) →ₙ+* R`, `Φ(A) = ∑_{i,j<r} a_i A_{ij} b_j`, injective.
* `ReturnTowerUnits.unitizeGL n : GL_n(M_r(P_C)) →* GL_n(R)`, `g ↦ (1 - Φ(1)) I_n + Φ_n(g)`,
  injective, and `flatUnitizeGL n : GL_{n×r}(P_C) →* GL_n(R)` after block flattening.
* `map_elementaryGroup_le`, `map_flat_elementaryGroup_le` (`n` nontrivial, printed `n ≥ 2`):
  the elementary groups land in `EL_n(R)`.
-/

namespace GroupApproximation.ChainCore

open MFQuotientUnits

/-- **A return tower** of height `N` and full base rank `r`: levels `a i`, `b i` with
`b i * a j = 0` for `i ≠ j`, `∑ i, a i * b i = 1`, all passing through the base idempotent `p`,
and `b i * a i = p` for the first `r` levels (tex 1727–1734). -/
structure ReturnTowerUnits (R : Type*) [Ring R] (N r : ℕ) where
  /-- The base idempotent, printed `p_C = 1_C`. -/
  p : R
  /-- The levels `a_i = u^i 1_{D_i}`. -/
  a : Fin N → R
  /-- The levels `b_i = 1_{D_i} u^{-i}`. -/
  b : Fin N → R
  le : r ≤ N
  isIdempotentElem_p : IsIdempotentElem p
  a_mul_p : ∀ i, a i * p = a i
  p_mul_b : ∀ i, p * b i = b i
  b_mul_a_of_ne : ∀ i j, i ≠ j → b i * a j = 0
  sum_a_mul_b : ∑ i, a i * b i = 1
  b_mul_a_of_lt : ∀ i : Fin N, (i : ℕ) < r → b i * a i = p

namespace ReturnTowerUnits

variable {R : Type*} [Ring R] {N r : ℕ} (τ : ReturnTowerUnits R N r)

/-- The return ring `P_C = p_C R p_C`. -/
abbrev Base : Type _ := Corner R τ.p τ.isIdempotentElem_p

theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → τ.Base) :
    ((∑ i ∈ s, f i : τ.Base) : R) = ∑ i ∈ s, (f i : R) :=
  map_sum (cornerInclusion τ.p τ.isIdempotentElem_p) f s

theorem p_mul_coe (x : τ.Base) : τ.p * (x : R) = x := x.2.1

theorem coe_mul_p (x : τ.Base) : (x : R) * τ.p = x := x.2.2

theorem a_mul_b_mul_a (i : Fin N) : τ.a i * (τ.b i * τ.a i) = τ.a i := by
  have h : (∑ j, τ.a j * τ.b j) * τ.a i = τ.a i := by rw [τ.sum_a_mul_b, one_mul]
  rw [Finset.sum_mul, Finset.sum_eq_single i (fun j _ hj => by
    rw [mul_assoc, τ.b_mul_a_of_ne j i hj, mul_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)] at h
  rwa [mul_assoc] at h

theorem b_mul_a_mul_b (i : Fin N) : τ.b i * τ.a i * τ.b i = τ.b i := by
  have h : τ.b i * (∑ j, τ.a j * τ.b j) = τ.b i := by rw [τ.sum_a_mul_b, mul_one]
  rw [Finset.mul_sum, Finset.sum_eq_single i (fun j _ hj => by
    rw [← mul_assoc, τ.b_mul_a_of_ne i j (Ne.symm hj), zero_mul])
    (fun hi => absurd (Finset.mem_univ i) hi)] at h
  rwa [← mul_assoc] at h

theorem mem_corner (i j : Fin N) (x : R) :
    τ.b i * x * τ.a j ∈ cornerNonUnitalSubring τ.p τ.isIdempotentElem_p := by
  refine mem_cornerNonUnitalSubring_iff.2 ⟨?_, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, τ.p_mul_b]
  · rw [mul_assoc, τ.a_mul_p]

/-! ### `R` is a unital corner of `M_N(P_C)` -/

theorem b_mul_mul_a (i j : Fin N) (x y : R) :
    τ.b i * (x * y) * τ.a j = ∑ l, τ.b i * x * τ.a l * (τ.b l * y * τ.a j) := by
  have hxy : x * y = x * (∑ l, τ.a l * τ.b l) * y := by rw [τ.sum_a_mul_b, mul_one]
  rw [hxy, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [mul_assoc]

/-- **`x ↦ (b_i x a_j)_{ij}`** (tex 1733), a homomorphism of non-unital rings. -/
def toMatrix : R →ₙ+* Matrix (Fin N) (Fin N) τ.Base where
  toFun x := Matrix.of fun i j => ⟨τ.b i * x * τ.a j, τ.mem_corner i j x⟩
  map_mul' x y := Matrix.ext fun i j => corner_ext <| by
    rw [Matrix.mul_apply, τ.coe_sum]
    simp only [Matrix.of_apply, coe_corner_mul]
    exact τ.b_mul_mul_a i j x y
  map_zero' := Matrix.ext fun i j => corner_ext <| by
    simp only [Matrix.of_apply, mul_zero, zero_mul, Matrix.zero_apply, coe_corner_zero]
  map_add' x y := Matrix.ext fun i j => corner_ext <| by
    simp only [Matrix.of_apply, mul_add, add_mul, Matrix.add_apply, coe_corner_add]

theorem toMatrix_apply (x : R) (i j : Fin N) :
    ((τ.toMatrix x i j : τ.Base) : R) = τ.b i * x * τ.a j :=
  rfl

theorem eq_sum_toMatrix (x : R) :
    x = ∑ i, ∑ j, τ.a i * (τ.toMatrix x i j : R) * τ.b j := by
  simp only [toMatrix_apply]
  calc x = (∑ i, τ.a i * τ.b i) * x * (∑ j, τ.a j * τ.b j) := by
        rw [τ.sum_a_mul_b, one_mul, mul_one]
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [mul_assoc]

theorem toMatrix_injective : Function.Injective τ.toMatrix := fun x y h =>
  calc x = ∑ i, ∑ j, τ.a i * (τ.toMatrix x i j : R) * τ.b j := τ.eq_sum_toMatrix x
    _ = ∑ i, ∑ j, τ.a i * (τ.toMatrix y i j : R) * τ.b j := by rw [h]
    _ = y := (τ.eq_sum_toMatrix y).symm

theorem isIdempotentElem_toMatrix_one : IsIdempotentElem (τ.toMatrix 1) := by
  show τ.toMatrix 1 * τ.toMatrix 1 = τ.toMatrix 1
  rw [← map_mul, mul_one]

theorem toMatrix_mem_corner (x : R) :
    τ.toMatrix x ∈
      cornerNonUnitalSubring (τ.toMatrix 1) τ.isIdempotentElem_toMatrix_one :=
  mem_cornerNonUnitalSubring_iff.2 ⟨by rw [← map_mul, one_mul], by rw [← map_mul, mul_one]⟩

theorem coe_toMatrix_one_mul (M : Matrix (Fin N) (Fin N) τ.Base) (k l : Fin N) :
    ((τ.toMatrix 1 * M) k l : R) = τ.b k * τ.a k * (M k l : R) := by
  rw [Matrix.mul_apply, τ.coe_sum, Finset.sum_eq_single k]
  · simp only [coe_corner_mul, toMatrix_apply, mul_one]
  · intro m _ hm
    rw [coe_corner_mul, toMatrix_apply, mul_one, τ.b_mul_a_of_ne k m (Ne.symm hm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem coe_mul_toMatrix_one (M : Matrix (Fin N) (Fin N) τ.Base) (k l : Fin N) :
    ((M * τ.toMatrix 1) k l : R) = (M k l : R) * (τ.b l * τ.a l) := by
  rw [Matrix.mul_apply, τ.coe_sum, Finset.sum_eq_single l]
  · simp only [coe_corner_mul, toMatrix_apply, mul_one]
  · intro m _ hm
    rw [coe_corner_mul, toMatrix_apply, mul_one, τ.b_mul_a_of_ne m l hm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-- The inverse of `toMatrix` on the corner: `M ↦ ∑_{i,j} a_i M_{ij} b_j`. -/
def ofMatrix (M : Matrix (Fin N) (Fin N) τ.Base) : R :=
  ∑ i, ∑ j, τ.a i * (M i j : R) * τ.b j

theorem toMatrix_ofMatrix (M : Matrix (Fin N) (Fin N) τ.Base)
    (h₁ : τ.toMatrix 1 * M = M) (h₂ : M * τ.toMatrix 1 = M) :
    τ.toMatrix (τ.ofMatrix M) = M := by
  refine Matrix.ext fun k l => corner_ext ?_
  have e₁ : τ.b k * τ.a k * (M k l : R) = M k l := by rw [← τ.coe_toMatrix_one_mul, h₁]
  have e₂ : (M k l : R) * (τ.b l * τ.a l) = M k l := by rw [← τ.coe_mul_toMatrix_one, h₂]
  rw [toMatrix_apply, ofMatrix, Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single k]
  · rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l]
    · calc τ.b k * (τ.a k * (M k l : R) * τ.b l) * τ.a l
          = (τ.b k * τ.a k * (M k l : R)) * (τ.b l * τ.a l) := by simp only [mul_assoc]
        _ = M k l := by rw [e₁, e₂]
    · intro j _ hj
      rw [show τ.b k * (τ.a k * (M k j : R) * τ.b j) * τ.a l =
          τ.b k * τ.a k * (M k j : R) * (τ.b j * τ.a l) by simp only [mul_assoc],
        τ.b_mul_a_of_ne j l hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h
  · intro i _ hi
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show τ.b k * (τ.a i * (M i j : R) * τ.b j) * τ.a l =
        (τ.b k * τ.a i) * ((M i j : R) * τ.b j * τ.a l) by simp only [mul_assoc],
      τ.b_mul_a_of_ne k i (Ne.symm hi), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- `toMatrix` as a unital ring homomorphism into the corner `E M_N(P_C) E`, `E = toMatrix 1`. -/
def toCorner :
    R →+* Corner (Matrix (Fin N) (Fin N) τ.Base) (τ.toMatrix 1) τ.isIdempotentElem_toMatrix_one where
  toFun x := ⟨τ.toMatrix x, τ.toMatrix_mem_corner x⟩
  map_one' := rfl
  map_mul' x y := corner_ext (map_mul τ.toMatrix x y)
  map_zero' := corner_ext (map_zero τ.toMatrix)
  map_add' x y := corner_ext (map_add τ.toMatrix x y)

theorem toCorner_bijective : Function.Bijective τ.toCorner := by
  refine ⟨fun x y h => τ.toMatrix_injective (congrArg Subtype.val h), fun z => ⟨τ.ofMatrix z.1, ?_⟩⟩
  exact corner_ext (τ.toMatrix_ofMatrix z.1 z.2.1 z.2.2)

/-- **`R` is a unital corner of `M_N(P_C)`** (tex 1732–1733). -/
noncomputable def cornerEquiv :
    R ≃+* Corner (Matrix (Fin N) (Fin N) τ.Base) (τ.toMatrix 1) τ.isIdempotentElem_toMatrix_one :=
  RingEquiv.ofBijective τ.toCorner τ.toCorner_bijective

/-- If `M_N(P_C)` is directly finite, so is `R`: the corner of a directly finite ring is directly
finite, and `R` is such a corner. -/
theorem isDedekindFiniteMonoid [IsDedekindFiniteMonoid (Matrix (Fin N) (Fin N) τ.Base)] :
    IsDedekindFiniteMonoid R :=
  IsDedekindFiniteMonoid.of_injective τ.toCorner.toMonoidHom τ.toCorner_bijective.1

/-! ### The first `r` levels: `Φ : M_r(P_C) → R` -/

/-- The first `r` levels, as indices of the tower. -/
def lo (i : Fin r) : Fin N :=
  Fin.castLE τ.le i

theorem b_mul_a_lo (i j : Fin r) : τ.b (τ.lo i) * τ.a (τ.lo j) = if i = j then τ.p else 0 := by
  split_ifs with h
  · subst h
    exact τ.b_mul_a_of_lt _ (by simp [lo])
  · exact τ.b_mul_a_of_ne _ _ fun e => h (Fin.ext (by simpa [lo] using congrArg Fin.val e))

/-- `Φ(A) = ∑_{i,j<r} a_i A_{ij} b_j`. -/
def phiFun (A : Matrix (Fin r) (Fin r) τ.Base) : R :=
  ∑ i, ∑ j, τ.a (τ.lo i) * (A i j : R) * τ.b (τ.lo j)

theorem b_mul_phiFun (A : Matrix (Fin r) (Fin r) τ.Base) (k : Fin r) :
    τ.b (τ.lo k) * τ.phiFun A = ∑ j, (A k j : R) * τ.b (τ.lo j) := by
  rw [phiFun, Finset.mul_sum, Finset.sum_eq_single k]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show τ.b (τ.lo k) * (τ.a (τ.lo k) * (A k j : R) * τ.b (τ.lo j)) =
        τ.b (τ.lo k) * τ.a (τ.lo k) * (A k j : R) * τ.b (τ.lo j) by simp only [mul_assoc],
      τ.b_mul_a_lo, if_pos rfl, p_mul_coe]
  · intro i _ hi
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show τ.b (τ.lo k) * (τ.a (τ.lo i) * (A i j : R) * τ.b (τ.lo j)) =
        τ.b (τ.lo k) * τ.a (τ.lo i) * ((A i j : R) * τ.b (τ.lo j)) by simp only [mul_assoc],
      τ.b_mul_a_lo, if_neg (Ne.symm hi), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem b_mul_phiFun_mul_a (A : Matrix (Fin r) (Fin r) τ.Base) (k l : Fin r) :
    τ.b (τ.lo k) * τ.phiFun A * τ.a (τ.lo l) = A k l := by
  rw [τ.b_mul_phiFun, Finset.sum_mul, Finset.sum_eq_single l]
  · rw [mul_assoc, τ.b_mul_a_lo, if_pos rfl, coe_mul_p]
  · intro j _ hj
    rw [mul_assoc, τ.b_mul_a_lo, if_neg hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem phiFun_mul (A B : Matrix (Fin r) (Fin r) τ.Base) :
    τ.phiFun (A * B) = τ.phiFun A * τ.phiFun B := by
  show (∑ i, ∑ j, τ.a (τ.lo i) * ((A * B) i j : R) * τ.b (τ.lo j)) =
    (∑ i, ∑ j, τ.a (τ.lo i) * (A i j : R) * τ.b (τ.lo j)) * τ.phiFun B
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hR : (∑ j, τ.a (τ.lo i) * (A i j : R) * τ.b (τ.lo j)) * τ.phiFun B =
      ∑ j, ∑ l, τ.a (τ.lo i) * (A i j : R) * (B j l : R) * τ.b (τ.lo l) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc, τ.b_mul_phiFun, Finset.mul_sum]
  have hL : ∀ j, τ.a (τ.lo i) * ((A * B) i j : R) * τ.b (τ.lo j) =
      ∑ l, τ.a (τ.lo i) * (A i l : R) * (B l j : R) * τ.b (τ.lo j) := fun j => by
    rw [Matrix.mul_apply, τ.coe_sum]
    simp only [coe_corner_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [hR]
  simp only [hL]
  exact Finset.sum_comm

theorem phiFun_add (A B : Matrix (Fin r) (Fin r) τ.Base) :
    τ.phiFun (A + B) = τ.phiFun A + τ.phiFun B := by
  simp only [phiFun, Matrix.add_apply, coe_corner_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem phiFun_zero : τ.phiFun 0 = 0 := by
  simp only [phiFun, Matrix.zero_apply, coe_corner_zero, mul_zero, zero_mul, Finset.sum_const_zero]

/-- **`Φ : M_r(P_C) → R`** (tex 1735–1737), a homomorphism of non-unital rings. -/
def phi : Matrix (Fin r) (Fin r) τ.Base →ₙ+* R where
  toFun := τ.phiFun
  map_mul' := τ.phiFun_mul
  map_zero' := τ.phiFun_zero
  map_add' := τ.phiFun_add

theorem phi_apply (A : Matrix (Fin r) (Fin r) τ.Base) :
    τ.phi A = ∑ i, ∑ j, τ.a (τ.lo i) * (A i j : R) * τ.b (τ.lo j) :=
  rfl

/-- `b_k Φ(A) a_l = A_{kl}`. -/
theorem b_mul_phi_mul_a (A : Matrix (Fin r) (Fin r) τ.Base) (k l : Fin r) :
    τ.b (τ.lo k) * τ.phi A * τ.a (τ.lo l) = A k l :=
  τ.b_mul_phiFun_mul_a A k l

/-- **`Φ` is injective** (tex 1735). -/
theorem phi_injective : Function.Injective τ.phi := fun A B h =>
  Matrix.ext fun k l => corner_ext <| by
    rw [← τ.b_mul_phi_mul_a A k l, ← τ.b_mul_phi_mul_a B k l, h]

theorem phi_one : τ.phi 1 = ∑ i : Fin r, τ.a (τ.lo i) * τ.b (τ.lo i) := by
  rw [phi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, coe_cornerOne, τ.a_mul_p]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), coe_corner_zero, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem isIdempotentElem_phi_one : IsIdempotentElem (τ.phi 1) := by
  show τ.phi 1 * τ.phi 1 = τ.phi 1
  rw [← map_mul, mul_one]

theorem phi_one_mul (A : Matrix (Fin r) (Fin r) τ.Base) : τ.phi 1 * τ.phi A = τ.phi A := by
  rw [← map_mul, one_mul]

theorem phi_mul_one (A : Matrix (Fin r) (Fin r) τ.Base) : τ.phi A * τ.phi 1 = τ.phi A := by
  rw [← map_mul, mul_one]

/-! ### Unitization: `GL_n(M_r(P_C)) → GL_n(R)` -/

variable (n : Type*) [Fintype n] [DecidableEq n]

theorem diagonal_mul_map_phi (M : Matrix n n (Matrix (Fin r) (Fin r) τ.Base)) :
    Matrix.diagonal (fun _ => 1 - τ.phi 1) * M.map τ.phi = 0 := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.map_apply, sub_mul, one_mul, τ.phi_one_mul, sub_self,
    Matrix.zero_apply]

theorem map_phi_mul_diagonal (M : Matrix n n (Matrix (Fin r) (Fin r) τ.Base)) :
    M.map τ.phi * Matrix.diagonal (fun _ => 1 - τ.phi 1) = 0 := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.map_apply, mul_sub, mul_one, τ.phi_mul_one, sub_self,
    Matrix.zero_apply]

theorem diagonal_mul_diagonal_one_sub :
    Matrix.diagonal (fun _ : n => 1 - τ.phi 1) * Matrix.diagonal (fun _ : n => 1 - τ.phi 1) =
      Matrix.diagonal (fun _ : n => 1 - τ.phi 1) := by
  rw [Matrix.diagonal_mul_diagonal, (IsIdempotentElem.one_sub τ.isIdempotentElem_phi_one).eq]

/-- `M ↦ (1 - Φ(1)) I_n + Φ_n(M)`. -/
def unitizeFun (M : Matrix n n (Matrix (Fin r) (Fin r) τ.Base)) : Matrix n n R :=
  Matrix.diagonal (fun _ => 1 - τ.phi 1) + M.map τ.phi

/-- **Unitization** `M_n(M_r(P_C)) → M_n(R)`, a unital monoid homomorphism. -/
def unitize : Matrix n n (Matrix (Fin r) (Fin r) τ.Base) →* Matrix n n R where
  toFun := τ.unitizeFun n
  map_one' := by
    ext i j
    simp only [unitizeFun, Matrix.add_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Matrix.one_apply_ne h]
  map_mul' M M' := by
    simp only [unitizeFun]
    rw [Matrix.map_mul, add_mul, mul_add, mul_add, τ.diagonal_mul_diagonal_one_sub,
      τ.diagonal_mul_map_phi, τ.map_phi_mul_diagonal]
    abel

theorem unitize_apply (M : Matrix n n (Matrix (Fin r) (Fin r) τ.Base)) :
    τ.unitize n M = Matrix.diagonal (fun _ => 1 - τ.phi 1) + M.map τ.phi :=
  rfl

theorem unitize_injective : Function.Injective (τ.unitize n) := fun M M' h => by
  have h' : M.map τ.phi = M'.map τ.phi := by
    simpa only [unitize_apply, add_right_inj] using h
  exact Matrix.ext fun i j => τ.phi_injective (congrFun (congrFun h' i) j)

/-- **Unitization embeds `GL_n(M_r(P_C))` into `GL_n(R)`** (tex 1739). -/
def unitizeGL : (Matrix n n (Matrix (Fin r) (Fin r) τ.Base))ˣ →* (Matrix n n R)ˣ :=
  Units.map (τ.unitize n)

theorem coe_unitizeGL (g : (Matrix n n (Matrix (Fin r) (Fin r) τ.Base))ˣ) :
    ((τ.unitizeGL n g : (Matrix n n R)ˣ) : Matrix n n R) = τ.unitize n g :=
  rfl

theorem unitizeGL_injective : Function.Injective (τ.unitizeGL n) :=
  Units.map_injective (τ.unitize_injective n)

theorem unitizeGL_elementaryUnit (i j : n) (h : i ≠ j) (A : Matrix (Fin r) (Fin r) τ.Base) :
    τ.unitizeGL n (elementaryUnit i j h A) = elementaryUnit i j h (τ.phi A) := by
  apply Units.ext
  rw [coe_unitizeGL, unitize_apply]
  change Matrix.diagonal (fun _ => 1 - τ.phi 1) + (1 + Matrix.single i j A).map τ.phi =
    1 + Matrix.single i j (τ.phi A)
  ext k l
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.single_apply,
    map_add]
  by_cases hkl : k = l
  · subst hkl
    have hc : ¬(i = k ∧ j = k) := fun e => h (e.1.trans e.2.symm)
    simp [hc]
  · by_cases hc : i = k ∧ j = l
    · simp [hkl, hc, Matrix.one_apply_ne hkl]
    · simp [hkl, hc, Matrix.one_apply_ne hkl]

theorem map_elementaryGroup_le :
    (elementaryGroup n (Matrix (Fin r) (Fin r) τ.Base)).map (τ.unitizeGL n) ≤
      elementaryGroup n R := by
  rw [elementaryGroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨i, j, h, A, rfl⟩
  show τ.unitizeGL n (elementaryUnit i j h A) ∈ elementaryGroup n R
  rw [τ.unitizeGL_elementaryUnit]
  exact elementaryUnit_mem i j h _

/-- Unitization after block flattening, `GL_{n×r}(P_C) → GL_n(R)`. -/
def flatUnitizeGL : (Matrix (n × Fin r) (n × Fin r) τ.Base)ˣ →* (Matrix n n R)ˣ :=
  (τ.unitizeGL n).comp
    (elementaryBlockUnitEquiv (ι := n) (κ := Fin r) (R := τ.Base)).symm.toMonoidHom

theorem flatUnitizeGL_injective : Function.Injective (τ.flatUnitizeGL n) :=
  (τ.unitizeGL_injective n).comp
    (elementaryBlockUnitEquiv (ι := n) (κ := Fin r) (R := τ.Base)).symm.injective

theorem flatUnitizeGL_comp_block :
    (τ.flatUnitizeGL n).comp
        (elementaryBlockUnitEquiv (ι := n) (κ := Fin r) (R := τ.Base)).toMonoidHom =
      τ.unitizeGL n :=
  MonoidHom.ext fun g => by
    simp only [flatUnitizeGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]

/-- **Block elementary flattening puts the image of `EL_{nr}(P_C)` inside `EL_n(R)`**
(tex 1740–1741), for nontrivial `n` (printed `n ≥ 2`). -/
theorem map_flat_elementaryGroup_le [Nontrivial n] :
    (elementaryGroup (n × Fin r) τ.Base).map (τ.flatUnitizeGL n) ≤ elementaryGroup n R := by
  rw [← elementaryBlockGroup_map (ι := n) (κ := Fin r) (R := τ.Base), Subgroup.map_map,
    τ.flatUnitizeGL_comp_block]
  exact τ.map_elementaryGroup_le n

end ReturnTowerUnits

end GroupApproximation.ChainCore

open GroupApproximation.ChainCore

#audit_axioms ReturnTowerUnits.cornerEquiv
#audit_axioms ReturnTowerUnits.isDedekindFiniteMonoid
#audit_axioms ReturnTowerUnits.phi_injective
#audit_axioms ReturnTowerUnits.unitizeGL_injective
#audit_axioms ReturnTowerUnits.flatUnitizeGL_injective
#audit_axioms ReturnTowerUnits.map_flat_elementaryGroup_le
