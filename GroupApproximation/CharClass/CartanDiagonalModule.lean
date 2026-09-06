import GroupApproximation.CharClass.CartanGroupRing
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# `W ⊗ S(X)`, built by hand over `F₂`

The internal Cartan-formula route (no Eilenberg–Zilber, no products of spaces)
needs the source functor `X ↦ W ⊗ S(X)` of the acyclic-models comparison,
where the tensor is taken over `ZMod 2`, **not** over the group ring `Λ`
(`CartanGroupRing.GroupRingZ2`) — using Mathlib's monoidal tensor of
`ChainComplex (ModuleCat Λ) ℕ` here would tensor `Λ`-linearly and collapse
`Λ ⊗_Λ (S(X)_{k-i})` down to `S(X)_{k-i})` itself, discarding exactly the
extra copies the group ring is there to provide.  So this file builds the
degreewise Finsupp module directly.

## Indexing

A generator of `(W ⊗ S(X))_k` is a pair `(i, σ)` with `i ≤ k` and `σ` a
singular `(k - i)`-simplex of `X` — `e_i ⊗ σ`.  Indexing this **by the
simplex's own degree** `n := k - i` rather than by `i` removes every
subtraction from `σ`'s type: `σ : stdSimplexTop n ⟶ X` depends only on `n`,
the same `n` before and after the degree-`0` part of the differential acts.
The `W`-index `i = k - n` is recovered only where it is actually needed (the
`(1 + t)` coefficient), and even there only as a *value*, not as part of a
type.  This is what makes the differential formula below free of any
`σ`-valued cast beyond the single, unavoidable one where the simplex's degree
itself changes (the boundary term).

## The differential

`wDiffGen` is the value of the differential on one generator `(n, σ)` with
`n : Fin (k + 2)` (a generator of `(W ⊗ S(X))_{k+1}`, since a simplex of degree
`n ≤ k + 1` pairs with `W`-index `k + 1 - n`):

* if `n ≤ k` (i.e. the `W`-index `k + 1 - n ≥ 1`): the term
  `(1 + t) • (e_{k-n} ⊗ σ)`, landing in bidegree `(k - n, n)`, i.e. at the
  *same* simplex-degree index `n`, now read in `(W ⊗ S(X))_k`;
* if `n ≥ 1` (so `σ` has a boundary): the term `e_{k+1-n} ⊗ ∂σ`, landing at
  simplex-degree `n - 1`, same `W`-index, expanded over the (mod-2) support of
  `∂σ` and converted from `ZMod 2` to `Λ` coefficients along the structure map.

Both conditions can hold at once (an interior degree); both can fail at once
only when `k = 0` and `n = 0`, in which case the differential out of the sole
generator is `0`, as it must be.
-/

open CategoryTheory Simplicial

namespace GroupApproximation.CharClass

/-- The standard topological `n`-simplex: the model of the acyclic-models
comparison, and the same model underlying Mathlib's singular chain complex
functor (`SimplexCategory.toTop.obj ⦋n⦌` is definitionally what a singular
`n`-simplex of `X` is a map out of). -/
noncomputable def stdSimplexTop (n : ℕ) : TopCat.{0} := SimplexCategory.toTop.obj (⦋n⦌ : SimplexCategory)

/-- The (mod-2) singular boundary, abstractly: for every space and degree, a
`ZMod 2`-linear map dropping the degree by one, natural in the space, squaring
to zero. This is exactly the shape of the differential of the singular chain
complex with `ZMod 2` coefficients; it is kept abstract here, rather than
identified on the nose with Mathlib's categorical-coproduct presentation of
that complex, so that the construction below can be checked without first
resolving that identification (see the lane report). -/
structure SingularBoundaryData where
  /-- The boundary map `C_{n+1}(X; F₂) → C_n(X; F₂)`, in the Finsupp
  presentation of the free module on singular simplices. -/
  bd : ∀ (X : TopCat.{0}) (n : ℕ),
    ((stdSimplexTop (n + 1) ⟶ X) →₀ ZMod 2) →ₗ[ZMod 2] ((stdSimplexTop n ⟶ X) →₀ ZMod 2)
  /-- Naturality in the space. -/
  bd_natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
      (c : (stdSimplexTop (n + 1) ⟶ X) →₀ ZMod 2),
      bd Y n (Finsupp.mapDomain (· ≫ f) c) = Finsupp.mapDomain (· ≫ f) (bd X n c)
  /-- `∂ ∘ ∂ = 0`. -/
  bd_bd : ∀ (X : TopCat.{0}) (n : ℕ) (c : (stdSimplexTop (n + 2) ⟶ X) →₀ ZMod 2),
      bd X n (bd X (n + 1) c) = 0

variable (data : SingularBoundaryData)

/-- The basis index of `(W ⊗ S(X))_k`: a simplex degree `n ≤ k` together with
an `n`-simplex of `X`.  The implicit `W`-index is `k - n`. -/
abbrev WSIndex (k : ℕ) (X : TopCat.{0}) : Type := Σ n : Fin (k + 1), stdSimplexTop n.val ⟶ X

/-- The underlying type of `(W ⊗ S(X))_k`: the free `Λ`-module on `WSIndex`.

Both this and `WSIndex` are `abbrev`, i.e. reducible, deliberately: `rw` checks
type-correctness at `instances` transparency and will not unfold a plain `def`,
so a semireducible `WSIndex` makes every goal mentioning `p.1` for
`p : WSIndex k X` untouchable by `rw`. -/
abbrev WTensorSMod (X : TopCat.{0}) (k : ℕ) : Type := WSIndex k X →₀ GroupRingZ2

/-! ## The differential, split into its two halves

Both halves are defined by a `Fin` eliminator rather than by an `if`, and that
is what keeps them free of casts.  `(Fin.castSucc j).val = j.val` and
`(Fin.succ m).val = m.val + 1` are both `rfl`, so in each branch the simplex
already has exactly the degree the target index wants; an `if` on
`n.val ≤ k` would not carry that information and would force a transport of the
simplex, i.e. a dependent proof argument inside a definition, which blocks every
later rewrite. -/

/-- The `W`-half of the differential on a generator: multiply by `1 + t` and drop
the `W`-index by one, keeping the simplex.  Absent exactly when the `W`-index is
already `0`, which is the `Fin.last` branch. -/
noncomputable def wDiffW (X : TopCat.{0}) (k : ℕ) :
    ∀ n : Fin (k + 2), (stdSimplexTop n.val ⟶ X) → WTensorSMod X k :=
  Fin.lastCases (motive := fun n : Fin (k + 2) => (stdSimplexTop n.val ⟶ X) → WTensorSMod X k)
    (fun _ => 0)
    (fun j σ => (1 + groupRingGen) • Finsupp.single (⟨j, σ⟩ : WSIndex k X) (1 : GroupRingZ2))

@[simp] theorem wDiffW_last (X : TopCat.{0}) (k : ℕ)
    (σ : stdSimplexTop (Fin.last (k + 1)).val ⟶ X) : wDiffW X k (Fin.last (k + 1)) σ = 0 := by
  rw [wDiffW, Fin.lastCases_last]

@[simp] theorem wDiffW_castSucc (X : TopCat.{0}) (k : ℕ) (j : Fin (k + 1))
    (σ : stdSimplexTop (Fin.castSucc j).val ⟶ X) :
    wDiffW X k (Fin.castSucc j) σ
      = (1 + groupRingGen) • Finsupp.single (⟨j, σ⟩ : WSIndex k X) (1 : GroupRingZ2) := by
  rw [wDiffW, Fin.lastCases_castSucc]

/-- The simplicial half of the differential on a generator: the boundary of the
simplex, keeping the `W`-index.  Absent exactly in simplex degree `0`, which is
the `Fin.cases` zero branch. -/
noncomputable def wDiffS (data : SingularBoundaryData) (X : TopCat.{0}) (k : ℕ) :
    ∀ n : Fin (k + 2), (stdSimplexTop n.val ⟶ X) → WTensorSMod X k :=
  Fin.cases (motive := fun n : Fin (k + 2) => (stdSimplexTop n.val ⟶ X) → WTensorSMod X k)
    (fun _ => 0)
    (fun m σ => Finsupp.mapDomain (fun τ => (⟨m, τ⟩ : WSIndex k X))
      (Finsupp.mapRange (algebraMap (ZMod 2) GroupRingZ2) (map_zero _)
        (data.bd X m.val (Finsupp.single σ (1 : ZMod 2)))))

@[simp] theorem wDiffS_zero (X : TopCat.{0}) (k : ℕ)
    (σ : stdSimplexTop (0 : Fin (k + 2)).val ⟶ X) : wDiffS data X k 0 σ = 0 := by
  rw [wDiffS, Fin.cases_zero]

@[simp] theorem wDiffS_succ (X : TopCat.{0}) (k : ℕ) (m : Fin (k + 1))
    (σ : stdSimplexTop (Fin.succ m).val ⟶ X) :
    wDiffS data X k (Fin.succ m) σ
      = Finsupp.mapDomain (fun τ => (⟨m, τ⟩ : WSIndex k X))
          (Finsupp.mapRange (algebraMap (ZMod 2) GroupRingZ2) (map_zero _)
            (data.bd X m.val (Finsupp.single σ (1 : ZMod 2)))) := by
  rw [wDiffS, Fin.cases_succ]

/-- The value of the differential on one generator `e_{k+1-n} ⊗ σ` of degree
`k + 1`. -/
noncomputable def wDiffGen (data : SingularBoundaryData) (X : TopCat.{0}) (k : ℕ)
    (n : Fin (k + 2)) (σ : stdSimplexTop n.val ⟶ X) : WTensorSMod X k :=
  wDiffW X k n σ + wDiffS data X k n σ

/-- The differential of `W ⊗ S(X)`, as a `Λ`-linear map. -/
noncomputable def wDiff (data : SingularBoundaryData) (X : TopCat.{0}) (k : ℕ) :
    WTensorSMod X (k + 1) →ₗ[GroupRingZ2] WTensorSMod X k :=
  Finsupp.linearCombination GroupRingZ2 (fun p : WSIndex (k + 1) X => wDiffGen data X k p.1 p.2)

@[simp] theorem wDiff_single (data : SingularBoundaryData) (X : TopCat.{0}) (k : ℕ)
    (p : WSIndex (k + 1) X) :
    wDiff data X k (Finsupp.single p (1 : GroupRingZ2)) = wDiffGen data X k p.1 p.2 := by
  rw [wDiff, Finsupp.linearCombination_single, one_smul]

end GroupApproximation.CharClass
