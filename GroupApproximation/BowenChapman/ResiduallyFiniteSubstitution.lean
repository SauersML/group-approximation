import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

/-!
# Residual finiteness of exponent-substitution semidirect products

Let `k` be a finite commutative ring with `1 ≠ 0` and `ι` a finite type, and write
`k[ℤ^ι]` for `AddMonoidAlgebra k (ι → ℤ)`, the Laurent polynomials in the variables `ι`.
An integer matrix `M` acts on `k[ℤ^ι]` by the monomial substitution `x^v ↦ x^(M v)`
(`expSubst`).

`residuallyFinite_semidirectProduct_of_expSubst` states: let `N` be a subgroup of the units
of `Matrix ι ι k[ℤ^ι]`, `Q` a subgroup of the units of `Matrix ι ι ℤ`, and
`φ : Q →* MulAut N` an action that substitutes exponents entrywise.  Then `N ⋊[φ] Q` is
residually finite.

The finite quotients reduce exponents modulo `n`.  The ring `k[(ℤ/n)^ι]` is finite, and
`N ⋊[φ] Q` acts on the column vectors over it by `(A, M) · u = Ā *ᵥ σ̄_M(u)`, where `Ā`
reduces the exponents of the entries of `A` and `σ̄_M` substitutes exponents by `M mod n`
(`modPerm`).  An element acting trivially has `Ā = 1` (test the basis vectors) and
`M ≡ 1 mod n` (test monomial vectors).  A nontrivial `(A, M)` survives for a suitable `n`:
an entry of `M - 1` is a nonzero integer, and an entry of `A - 1` is a nonzero Laurent
polynomial whose finitely many exponents stay distinct modulo a large `n`.
-/

namespace GroupApproximation.BowenChapman.CongruenceQuotient

open scoped Matrix

noncomputable section

/-! ### Exponent maps -/

/-- Multiplication of column vectors by a square matrix, as an additive homomorphism. -/
def mulVecAddHom {R ι : Type*} [NonUnitalNonAssocSemiring R] [Fintype ι]
    (M : Matrix ι ι R) : (ι → R) →+ (ι → R) where
  toFun v := M *ᵥ v
  map_zero' := Matrix.mulVec_zero M
  map_add' := Matrix.mulVec_add M

@[simp] theorem mulVecAddHom_apply {R ι : Type*} [NonUnitalNonAssocSemiring R] [Fintype ι]
    (M : Matrix ι ι R) (v : ι → R) : mulVecAddHom M v = M *ᵥ v :=
  rfl

/-- Reduction of integer exponent vectors modulo `n`. -/
def expReduce (ι : Type*) (n : ℕ) : (ι → ℤ) →+ (ι → ZMod n) where
  toFun w i := (w i : ZMod n)
  map_zero' := by
    funext i
    simp
  map_add' w w' := by
    funext i
    simp

@[simp] theorem expReduce_apply (ι : Type*) (n : ℕ) (w : ι → ℤ) (i : ι) :
    expReduce ι n w i = (w i : ZMod n) :=
  rfl

/-- Reduction of exponents modulo `n`, from `k[ℤ^ι]` to `k[(ℤ/n)^ι]`. -/
def reduceExp (k : Type*) [CommRing k] (ι : Type*) (n : ℕ) :
    AddMonoidAlgebra k (ι → ℤ) →+* AddMonoidAlgebra k (ι → ZMod n) :=
  AddMonoidAlgebra.mapDomainRingHom k (expReduce ι n)

/-- The monomial substitution `x^v ↦ x^(M v)` by an integer matrix. -/
def expSubst (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] (M : Matrix ι ι ℤ) :
    AddMonoidAlgebra k (ι → ℤ) →+* AddMonoidAlgebra k (ι → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom k (mulVecAddHom M)

/-- The monomial substitution by a matrix over `ZMod n`, on `k[(ℤ/n)^ι]`. -/
def substMod (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] {n : ℕ}
    (R : Matrix ι ι (ZMod n)) :
    AddMonoidAlgebra k (ι → ZMod n) →+* AddMonoidAlgebra k (ι → ZMod n) :=
  AddMonoidAlgebra.mapDomainRingHom k (mulVecAddHom R)

theorem expSubst_single (k : Type*) [CommRing k] {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℤ) (v : ι → ℤ) (c : k) :
    expSubst k M (AddMonoidAlgebra.single v c) = AddMonoidAlgebra.single (M *ᵥ v) c := by
  show AddMonoidAlgebra.mapDomain (fun w => M *ᵥ w) (AddMonoidAlgebra.single v c) = _
  exact AddMonoidAlgebra.mapDomain_single

theorem substMod_single (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] {n : ℕ}
    (R : Matrix ι ι (ZMod n)) (w : ι → ZMod n) (c : k) :
    substMod k R (AddMonoidAlgebra.single w c) = AddMonoidAlgebra.single (R *ᵥ w) c := by
  show AddMonoidAlgebra.mapDomain (fun w' => R *ᵥ w') (AddMonoidAlgebra.single w c) = _
  exact AddMonoidAlgebra.mapDomain_single

/-- Reduction modulo `n` intertwines integer substitution with substitution modulo `n`. -/
theorem reduceExp_expSubst (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] (n : ℕ)
    (M : Matrix ι ι ℤ) (a : AddMonoidAlgebra k (ι → ℤ)) :
    reduceExp k ι n (expSubst k M a) =
      substMod k (M.map (Int.castRingHom (ZMod n))) (reduceExp k ι n a) := by
  have hhom : (expReduce ι n).comp (mulVecAddHom M) =
      (mulVecAddHom (M.map (Int.castRingHom (ZMod n)))).comp (expReduce ι n) :=
    AddMonoidHom.ext fun v => funext fun i =>
      RingHom.map_mulVec (Int.castRingHom (ZMod n)) M v i
  have hring : (reduceExp k ι n).comp (expSubst k M) =
      (substMod k (M.map (Int.castRingHom (ZMod n)))).comp (reduceExp k ι n) := by
    simp only [reduceExp, expSubst, substMod, ← AddMonoidAlgebra.mapDomainRingHom_comp, hhom]
  exact RingHom.congr_fun hring a

theorem substMod_mul_apply (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] {n : ℕ}
    (R S : Matrix ι ι (ZMod n)) (a : AddMonoidAlgebra k (ι → ZMod n)) :
    substMod k (R * S) a = substMod k R (substMod k S a) := by
  have hhom : mulVecAddHom (R * S) = (mulVecAddHom R).comp (mulVecAddHom S) :=
    AddMonoidHom.ext fun v => (Matrix.mulVec_mulVec v R S).symm
  have hring : substMod k (R * S) = (substMod k R).comp (substMod k S) := by
    simp only [substMod, hhom, AddMonoidAlgebra.mapDomainRingHom_comp]
  exact RingHom.congr_fun hring a

theorem substMod_one_apply (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (a : AddMonoidAlgebra k (ι → ZMod n)) :
    substMod k (1 : Matrix ι ι (ZMod n)) a = a := by
  have hhom : mulVecAddHom (1 : Matrix ι ι (ZMod n)) = AddMonoidHom.id (ι → ZMod n) :=
    AddMonoidHom.ext fun v => Matrix.one_mulVec v
  have hring : substMod k (1 : Matrix ι ι (ZMod n)) = RingHom.id _ := by
    simp only [substMod, hhom, AddMonoidAlgebra.mapDomainRingHom_id]
  rw [hring, RingHom.id_apply]

/-! ### Reduced matrices -/

/-- Reduce the exponents of every entry of an invertible Laurent matrix modulo `n`. -/
def reduceMatrix (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (A : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
    Matrix ι ι (AddMonoidAlgebra k (ι → ZMod n)) :=
  (A : Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))).map (reduceExp k ι n)

/-- Reduce an invertible integer matrix modulo `n`. -/
def reduceIntMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (M : (Matrix ι ι ℤ)ˣ) :
    Matrix ι ι (ZMod n) :=
  (M : Matrix ι ι ℤ).map (Int.castRingHom (ZMod n))

theorem reduceMatrix_mul (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (A B : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
    reduceMatrix k n (A * B) = reduceMatrix k n A * reduceMatrix k n B := by
  simp only [reduceMatrix, Units.val_mul, Matrix.map_mul]

theorem reduceMatrix_one (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) : reduceMatrix k n (1 : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) = 1 := by
  simp only [reduceMatrix, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem reduceIntMatrix_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (M S : (Matrix ι ι ℤ)ˣ) :
    reduceIntMatrix n (M * S) = reduceIntMatrix n M * reduceIntMatrix n S := by
  simp only [reduceIntMatrix, Units.val_mul, Matrix.map_mul]

theorem reduceIntMatrix_one {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    reduceIntMatrix n (1 : (Matrix ι ι ℤ)ˣ) = 1 := by
  simp only [reduceIntMatrix, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- If the action substitutes exponents entrywise, reduction turns it into entrywise
substitution modulo `n`. -/
theorem reduceMatrix_action {k ι : Type*} [CommRing k] [Fintype ι] [DecidableEq ι]
    {N : Subgroup (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ} {Q : Subgroup (Matrix ι ι ℤ)ˣ}
    (φ : ↥Q →* MulAut ↥N)
    (hφ : ∀ (M : ↥Q) (B : ↥N) (i j : ι),
      (((φ M B : ↥N) : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
          Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) i j =
        expSubst k ((M : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ)
          (((B : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
            Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) i j))
    (n : ℕ) (M : ↥Q) (B : ↥N) :
    reduceMatrix k n ((φ M B : ↥N) : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) =
      (reduceMatrix k n (B : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ)).map
        (substMod k (reduceIntMatrix n (M : (Matrix ι ι ℤ)ˣ))) := by
  ext i j
  simp only [reduceMatrix, reduceIntMatrix, Matrix.map_apply]
  rw [hφ M B i j, reduceExp_expSubst]

/-! ### The finite permutation representations -/

theorem one_mulVec_substMod_one (k : Type*) [CommRing k] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (n : ℕ) (u : ι → AddMonoidAlgebra k (ι → ZMod n)) :
    ((1 : Matrix ι ι (AddMonoidAlgebra k (ι → ZMod n))) *ᵥ
      fun i => substMod k (1 : Matrix ι ι (ZMod n)) (u i)) = u := by
  rw [Matrix.one_mulVec]
  funext i
  exact substMod_one_apply k (u i)

theorem mulVec_substMod_mul (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] {n : ℕ}
    (L₁ L₂ : Matrix ι ι (AddMonoidAlgebra k (ι → ZMod n))) (R₁ R₂ : Matrix ι ι (ZMod n))
    (u : ι → AddMonoidAlgebra k (ι → ZMod n)) :
    ((L₁ * L₂.map (substMod k R₁)) *ᵥ fun i => substMod k (R₁ * R₂) (u i)) =
      L₁ *ᵥ fun i => substMod k R₁ ((L₂ *ᵥ fun i' => substMod k R₂ (u i')) i) := by
  have hinner : (fun i => substMod k R₁ ((L₂ *ᵥ fun i' => substMod k R₂ (u i')) i)) =
      L₂.map (substMod k R₁) *ᵥ fun i => substMod k R₁ (substMod k R₂ (u i)) := by
    funext i
    exact RingHom.map_mulVec (substMod k R₁) L₂ (fun i' => substMod k R₂ (u i')) i
  have hvec : (fun i => substMod k (R₁ * R₂) (u i)) =
      fun i => substMod k R₁ (substMod k R₂ (u i)) := by
    funext i
    exact substMod_mul_apply k R₁ R₂ (u i)
  rw [hinner, hvec, Matrix.mulVec_mulVec]

/-- The action of `N ⋊[φ] Q` on column vectors over `k[(ℤ/n)^ι]`,
`(A, M) · u = Ā *ᵥ σ̄_M(u)`. -/
def modAct {k ι : Type*} [CommRing k] [Fintype ι] [DecidableEq ι]
    {N : Subgroup (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ} {Q : Subgroup (Matrix ι ι ℤ)ˣ}
    {φ : ↥Q →* MulAut ↥N} (n : ℕ) (g : SemidirectProduct ↥N ↥Q φ)
    (u : ι → AddMonoidAlgebra k (ι → ZMod n)) : ι → AddMonoidAlgebra k (ι → ZMod n) :=
  reduceMatrix k n (g.left : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) *ᵥ
    fun i => substMod k (reduceIntMatrix n (g.right : (Matrix ι ι ℤ)ˣ)) (u i)

theorem modAct_one {k ι : Type*} [CommRing k] [Fintype ι] [DecidableEq ι]
    {N : Subgroup (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ} {Q : Subgroup (Matrix ι ι ℤ)ˣ}
    {φ : ↥Q →* MulAut ↥N} (n : ℕ) (u : ι → AddMonoidAlgebra k (ι → ZMod n)) :
    modAct n (1 : SemidirectProduct ↥N ↥Q φ) u = u := by
  have key := one_mulVec_substMod_one k n u
  rw [← reduceMatrix_one k (ι := ι) n, ← reduceIntMatrix_one (ι := ι) n] at key
  exact key

theorem modAct_mul {k ι : Type*} [CommRing k] [Fintype ι] [DecidableEq ι]
    {N : Subgroup (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ} {Q : Subgroup (Matrix ι ι ℤ)ˣ}
    (φ : ↥Q →* MulAut ↥N)
    (hφ : ∀ (M : ↥Q) (B : ↥N) (i j : ι),
      (((φ M B : ↥N) : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
          Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) i j =
        expSubst k ((M : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ)
          (((B : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
            Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) i j))
    (n : ℕ) (g h : SemidirectProduct ↥N ↥Q φ) (u : ι → AddMonoidAlgebra k (ι → ZMod n)) :
    modAct n (g * h) u = modAct n g (modAct n h u) := by
  have hleft :
      reduceMatrix k n ((g * h).left : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) =
        reduceMatrix k n (g.left : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) *
          (reduceMatrix k n (h.left : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ)).map
            (substMod k (reduceIntMatrix n (g.right : (Matrix ι ι ℤ)ˣ))) := by
    rw [SemidirectProduct.mul_left, Subgroup.coe_mul, reduceMatrix_mul,
      reduceMatrix_action φ hφ]
  have hright : reduceIntMatrix n ((g * h).right : (Matrix ι ι ℤ)ˣ) =
      reduceIntMatrix n (g.right : (Matrix ι ι ℤ)ˣ) *
        reduceIntMatrix n (h.right : (Matrix ι ι ℤ)ˣ) := by
    rw [SemidirectProduct.mul_right, Subgroup.coe_mul, reduceIntMatrix_mul]
  have key := mulVec_substMod_mul k
    (reduceMatrix k n (g.left : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ))
    (reduceMatrix k n (h.left : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ))
    (reduceIntMatrix n (g.right : (Matrix ι ι ℤ)ˣ))
    (reduceIntMatrix n (h.right : (Matrix ι ι ℤ)ˣ)) u
  rw [← hleft, ← hright] at key
  exact key

/-- The finite permutation representation of `N ⋊[φ] Q` obtained by reducing exponents
modulo `n`. -/
def modPerm {k ι : Type*} [CommRing k] [Fintype ι] [DecidableEq ι]
    {N : Subgroup (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ} {Q : Subgroup (Matrix ι ι ℤ)ˣ}
    (φ : ↥Q →* MulAut ↥N)
    (hφ : ∀ (M : ↥Q) (B : ↥N) (i j : ι),
      (((φ M B : ↥N) : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
          Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) i j =
        expSubst k ((M : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ)
          (((B : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
            Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) i j))
    (n : ℕ) :
    SemidirectProduct ↥N ↥Q φ →* Equiv.Perm (ι → AddMonoidAlgebra k (ι → ZMod n)) where
  toFun g :=
    { toFun := modAct n g
      invFun := modAct n g⁻¹
      left_inv := fun u => by
        rw [← modAct_mul φ hφ, inv_mul_cancel, modAct_one]
      right_inv := fun u => by
        rw [← modAct_mul φ hφ, mul_inv_cancel, modAct_one] }
  map_one' := Equiv.ext fun u => modAct_one n u
  map_mul' g h := Equiv.ext fun u => modAct_mul φ hφ n g h u

/-! ### Detection -/

/-- An element acting trivially on all column vectors reduces to the identity. -/
theorem eq_one_of_forall_mulVec_substMod_eq {k ι : Type*} [CommRing k] [Nontrivial k]
    [Fintype ι] [DecidableEq ι] {n : ℕ} (L : Matrix ι ι (AddMonoidAlgebra k (ι → ZMod n)))
    (R : Matrix ι ι (ZMod n))
    (h : ∀ u : ι → AddMonoidAlgebra k (ι → ZMod n), (L *ᵥ fun i => substMod k R (u i)) = u) :
    L = 1 ∧ R = 1 := by
  have hL : L = 1 := by
    ext i j
    have hsingle :
        (fun i' => substMod k R
            ((Pi.single j 1 : ι → AddMonoidAlgebra k (ι → ZMod n)) i')) =
          (Pi.single j 1 : ι → AddMonoidAlgebra k (ι → ZMod n)) := by
      funext i'
      by_cases hi : i' = j
      · rw [hi, Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne hi, map_zero]
    have hcol := congrFun (h (Pi.single j 1)) i
    rw [hsingle, Matrix.mulVec_single_one, Matrix.col_apply] at hcol
    rw [hcol, Matrix.one_apply, Pi.single_apply]
  refine ⟨hL, ?_⟩
  ext i j
  have hvec := h fun _ => AddMonoidAlgebra.single (Pi.single j (1 : ZMod n)) (1 : k)
  rw [hL, Matrix.one_mulVec] at hvec
  have hmono : substMod k R (AddMonoidAlgebra.single (Pi.single j (1 : ZMod n)) (1 : k)) =
      AddMonoidAlgebra.single (Pi.single j (1 : ZMod n)) (1 : k) :=
    congrFun hvec i
  rw [substMod_single, AddMonoidAlgebra.single_left_inj one_ne_zero] at hmono
  have hcol := congrFun hmono i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at hcol
  rw [hcol, Matrix.one_apply, Pi.single_apply]

/-- A nonidentity integer matrix stays a nonidentity modulo some `n > 0`. -/
theorem exists_map_intCast_ne_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℤ} (hX : X ≠ 1) :
    ∃ n : ℕ, 0 < n ∧ X.map (Int.castRingHom (ZMod n)) ≠ 1 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, X i j ≠ (1 : Matrix ι ι ℤ) i j := by
    by_contra hcon
    exact hX (Matrix.ext fun i j => not_not.mp fun hne => hcon ⟨i, j, hne⟩)
  obtain ⟨d, hd⟩ : ∃ d : ℤ, X i j - (1 : Matrix ι ι ℤ) i j = d := ⟨_, rfl⟩
  refine ⟨d.natAbs + 1, Nat.succ_pos _, fun hmap => hij ?_⟩
  have h1 : ((X i j : ℤ) : ZMod (d.natAbs + 1)) =
      (1 : Matrix ι ι (ZMod (d.natAbs + 1))) i j :=
    congrFun (congrFun hmap i) j
  have h2 : (1 : Matrix ι ι (ZMod (d.natAbs + 1))) i j =
      (((1 : Matrix ι ι ℤ) i j : ℤ) : ZMod (d.natAbs + 1)) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub (X i j) ((1 : Matrix ι ι ℤ) i j)
    (d.natAbs + 1)).mp (h1.trans h2)
  have h4 := dvd_neg.mpr h3
  rw [neg_sub, hd] at h4
  have hlt : |d| < ((d.natAbs + 1 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_one, Int.natCast_natAbs]
    exact lt_add_one _
  have hzero := Int.eq_zero_of_abs_lt_dvd h4 hlt
  rw [← hd] at hzero
  exact sub_eq_zero.mp hzero

/-- A nonzero Laurent polynomial stays nonzero after reducing exponents modulo some
`n > 0`. -/
theorem exists_reduceExp_ne_zero {k ι : Type*} [CommRing k] [Fintype ι]
    {a : AddMonoidAlgebra k (ι → ℤ)} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ reduceExp k ι n a ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ : a.coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr fun hzero => ha (AddMonoidAlgebra.ext hzero)
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ w ∈ a.coeff.support, ∀ i, (w i).natAbs ≤ B := by
    refine ⟨∑ w ∈ a.coeff.support, ∑ i, (w i).natAbs, fun w hw i => ?_⟩
    have h1 : (w i).natAbs ≤ ∑ i', (w i').natAbs :=
      Finset.single_le_sum (f := fun i' => (w i').natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ i', (w i').natAbs ≤ ∑ w' ∈ a.coeff.support, ∑ i', (w' i').natAbs :=
      Finset.single_le_sum (f := fun w' : ι → ℤ => ∑ i', (w' i').natAbs)
        (fun _ _ => Nat.zero_le _) hw
    exact h1.trans h2
  refine ⟨2 * B + 1, Nat.succ_pos _, fun hzero => ?_⟩
  have hinj : Set.InjOn (expReduce ι (2 * B + 1)) (a.coeff.support : Set (ι → ℤ)) := by
    intro w hw w' hw' heq
    funext i
    have hi : ((w i : ℤ) : ZMod (2 * B + 1)) = ((w' i : ℤ) : ZMod (2 * B + 1)) :=
      congrFun heq i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
    have hw1 : |w i| ≤ (B : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hB w hw i
    have hw2 : |w' i| ≤ (B : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hB w' hw' i
    have hlt : |w' i - w i| < ((2 * B + 1 : ℕ) : ℤ) := by
      rw [abs_lt]
      obtain ⟨h1, h2⟩ := abs_le.mp hw1
      obtain ⟨h3, h4⟩ := abs_le.mp hw2
      push_cast
      constructor <;> linarith
    have hdiff := Int.eq_zero_of_abs_lt_dvd hi hlt
    linarith
  have hcoeff : (reduceExp k ι (2 * B + 1) a).coeff (expReduce ι (2 * B + 1) v) = a.coeff v :=
    Finsupp.mapDomain_apply' (a.coeff.support : Set (ι → ℤ)) a.coeff subset_rfl hinj hv
  have hv0 : a.coeff v = 0 :=
    hcoeff.symm.trans (congrArg (fun x : AddMonoidAlgebra k (ι → ZMod (2 * B + 1)) =>
      x.coeff (expReduce ι (2 * B + 1) v)) hzero)
  exact (Finsupp.mem_support_iff.mp hv) hv0

/-- A nonidentity Laurent matrix stays a nonidentity after reducing exponents modulo some
`n > 0`. -/
theorem exists_map_reduceExp_ne_one {k ι : Type*} [CommRing k] [Fintype ι] [DecidableEq ι]
    {Y : Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))} (hY : Y ≠ 1) :
    ∃ n : ℕ, 0 < n ∧ Y.map (reduceExp k ι n) ≠ 1 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, Y i j ≠ (1 : Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) i j := by
    by_contra hcon
    exact hY (Matrix.ext fun i j => not_not.mp fun hne => hcon ⟨i, j, hne⟩)
  obtain ⟨n, hn, hne⟩ := exists_reduceExp_ne_zero (sub_ne_zero.mpr hij)
  refine ⟨n, hn, fun hmap => hne ?_⟩
  have h1 : reduceExp k ι n (Y i j) =
      (1 : Matrix ι ι (AddMonoidAlgebra k (ι → ZMod n))) i j :=
    congrFun (congrFun hmap i) j
  rw [map_sub, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem finite_addMonoidAlgebra (k G : Type*) [Semiring k] [Finite k] [Finite G] :
    Finite (AddMonoidAlgebra k G) := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype G := Fintype.ofFinite G
  exact Finite.of_equiv (G →₀ k) AddMonoidAlgebra.coeffEquiv.symm

/-! ### Residual finiteness -/

/-- **Exponent-substitution semidirect products are residually finite.**  Let `N` be a
subgroup of the units of `Matrix ι ι k[ℤ^ι]` and `Q` a subgroup of the units of
`Matrix ι ι ℤ`, where `k` is a finite nontrivial commutative ring.  If `φ` substitutes
exponents entrywise, then `N ⋊[φ] Q` is residually finite. -/
theorem residuallyFinite_semidirectProduct_of_expSubst {k ι : Type} [CommRing k] [Finite k]
    [Nontrivial k] [Fintype ι] [DecidableEq ι]
    {N : Subgroup (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ} {Q : Subgroup (Matrix ι ι ℤ)ˣ}
    (φ : ↥Q →* MulAut ↥N)
    (hφ : ∀ (M : ↥Q) (B : ↥N) (i j : ι),
      (((φ M B : ↥N) : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
          Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) i j =
        expSubst k ((M : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ)
          (((B : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
            Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) i j)) :
    Group.ResiduallyFinite (SemidirectProduct ↥N ↥Q φ) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  obtain ⟨n, hn, hsep⟩ : ∃ n : ℕ, 0 < n ∧
      (reduceMatrix k n (g.left : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) ≠ 1 ∨
        reduceIntMatrix n (g.right : (Matrix ι ι ℤ)ˣ) ≠ 1) := by
    by_cases hl : g.left = 1
    · have hr : g.right ≠ 1 := fun hr => hg (SemidirectProduct.ext hl hr)
      have hX : ((g.right : (Matrix ι ι ℤ)ˣ) : Matrix ι ι ℤ) ≠ 1 := fun hX =>
        hr (Subtype.ext (Units.ext hX))
      obtain ⟨n, hn, hne⟩ := exists_map_intCast_ne_one hX
      exact ⟨n, hn, Or.inr hne⟩
    · have hY : ((g.left : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) :
          Matrix ι ι (AddMonoidAlgebra k (ι → ℤ))) ≠ 1 := fun hY =>
        hl (Subtype.ext (Units.ext hY))
      obtain ⟨n, hn, hne⟩ := exists_map_reduceExp_ne_one hY
      exact ⟨n, hn, Or.inl hne⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Finite (AddMonoidAlgebra k (ι → ZMod n)) := finite_addMonoidAlgebra k (ι → ZMod n)
  refine ⟨Equiv.Perm (ι → AddMonoidAlgebra k (ι → ZMod n)), inferInstance, inferInstance,
    modPerm φ hφ n, fun hone => ?_⟩
  have hfix : ∀ u : ι → AddMonoidAlgebra k (ι → ZMod n),
      (reduceMatrix k n (g.left : (Matrix ι ι (AddMonoidAlgebra k (ι → ℤ)))ˣ) *ᵥ
        fun i => substMod k (reduceIntMatrix n (g.right : (Matrix ι ι ℤ)ˣ)) (u i)) = u :=
    fun u => Equiv.congr_fun hone u
  obtain ⟨hL, hR⟩ := eq_one_of_forall_mulVec_substMod_eq _ _ hfix
  exact hsep.elim (fun hne => hne hL) (fun hne => hne hR)

end

end GroupApproximation.BowenChapman.CongruenceQuotient
