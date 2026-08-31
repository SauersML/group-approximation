import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionChainHomotopy
import Mathlib

/-!
# Iterated barycentric subdivision is chain-homotopic to the identity

This file proves that every iterate `sd^N` of barycentric subdivision is
chain-homotopic to the identity, and exposes an *explicit* accumulated homotopy
operator together with its chain-level boundary formula.  These explicit
formulas are needed by the later small-simplices theorem, which must control the
carrier/smallness of the homotopy witness, so the accumulated homotopy is kept
as a concrete degree-wise operator rather than hidden behind an existence
statement.

## Conventions

We use the composition convention

```text
sd^0 = 𝟙,   sd^(N+1) = sd ≫ sd^N
```

(`sd` applied first).  Since `sd` commutes with its own powers, this agrees with
`sd^N ≫ sd`.  Degree-wise this gives `(sd^(N+1))_n c = (sd^N)_n (sd_n c)`.

The accumulated homotopy is

```text
H^(0) = 0,   H^(N+1)_n = H^(N)_n + (sd^N)_{n+1} ∘ H_n,
```

i.e. `H^(N) = Σ_{r=0}^{N-1} sd^r ∘ H`, where `H =
barycentricSubdivisionHomotopyLinearMap` is the one-step homotopy operator from
prompt 08/09.

The boundary formula reads, with the project's index convention (the term
`H(∂ c)` packaged degree-wise exactly as `homotopyBoundaryTerm` was in prompt 09):

```text
c - sd^N(c) = ∂ (H^(N) c) + H^(N)(∂ c).
```

## Main results

* `barycentricSubdivisionIterChainMap` — the chain map `sd^N`.
* `barycentricSubdivisionIterLinearMap` — its degree-wise component as a linear map.
* `barycentricSubdivisionIterHomotopyLinearMap` — the explicit accumulated homotopy.
* `barycentricSubdivisionIter_chainHomotopic_id` — `Homotopy (sd^N) (𝟙 _)`.
* `barycentricSubdivisionIter_induces_identity_on_homology` — `sd^N` induces the
  identity on every homology group.
* `barycentricSubdivisionIter_boundary_formula` — the explicit chain-level
  boundary formula above.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-! ## 1. The iterated subdivision chain map -/

/-- The `N`-fold barycentric subdivision chain map `sd^N`, defined by
`sd^0 = 𝟙` and `sd^(N+1) = sd ≫ sd^N`. -/
noncomputable def barycentricSubdivisionIterChainMap
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    ℕ → (singularChainComplex R X ⟶ singularChainComplex R X)
  | 0 => 𝟙 _
  | (N+1) => barycentricSubdivisionChainMap R X ≫ barycentricSubdivisionIterChainMap R X N

@[simp] theorem barycentricSubdivisionIterChainMap_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    barycentricSubdivisionIterChainMap R X 0 = 𝟙 _ := rfl

theorem barycentricSubdivisionIterChainMap_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (N : ℕ) :
    barycentricSubdivisionIterChainMap R X (N+1)
      = barycentricSubdivisionChainMap R X ≫ barycentricSubdivisionIterChainMap R X N := rfl

/-- The degree-`n` component of `sd^N` as an `R`-linear map. -/
noncomputable def barycentricSubdivisionIterLinearMap
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) :
    singularChainGroup R X n →ₗ[R] singularChainGroup R X n :=
  ((barycentricSubdivisionIterChainMap R X N).f n).hom

/-- In iterate `0`, the degree-wise map is the identity. -/
theorem barycentricSubdivisionIterLinearMap_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterLinearMap R X 0 n c = c := by
  simp [barycentricSubdivisionIterLinearMap]

/-- The degree-wise successor formula `(sd^(N+1))_n c = (sd^N)_n (sd_n c)`. -/
theorem barycentricSubdivisionIterLinearMap_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterLinearMap R X (N+1) n c
      = barycentricSubdivisionIterLinearMap R X N n
          ((barycentricSubdivisionLinearMap R X n).hom c) := by
  simp [barycentricSubdivisionIterLinearMap, barycentricSubdivisionIterChainMap_succ]

/-- **`sd^N` commutes with the boundary** (degree-wise, pointwise form).  This is
the chain-map condition of `barycentricSubdivisionIterChainMap`. -/
theorem barycentricSubdivisionIterLinearMap_commutes_boundary
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) (c : singularChainGroup R X (n+1)) :
    (singularBoundary R X n).hom (barycentricSubdivisionIterLinearMap R X N (n+1) c)
      = barycentricSubdivisionIterLinearMap R X N n ((singularBoundary R X n).hom c) := by
  have h := (barycentricSubdivisionIterChainMap R X N).comm (n+1) n
  have h3 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h3
  simpa [barycentricSubdivisionIterLinearMap, singularBoundary] using h3

/-! ## 2. The accumulated homotopy operator -/

/-- The explicit accumulated homotopy operator
`H^(N) = Σ_{r=0}^{N-1} (sd^r) ∘ H`, defined by `H^(0) = 0` and
`H^(N+1)_n = H^(N)_n + (sd^N)_{n+1} ∘ H_n`. -/
noncomputable def barycentricSubdivisionIterHomotopyLinearMap
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    (N n : ℕ) → (singularChainGroup R X n →ₗ[R] singularChainGroup R X (n + 1))
  | 0, _ => 0
  | (N+1), n => barycentricSubdivisionIterHomotopyLinearMap R X N n
      + (barycentricSubdivisionIterLinearMap R X N (n+1)) ∘ₗ
          (barycentricSubdivisionHomotopyLinearMap R X n).hom

@[simp] theorem barycentricSubdivisionIterHomotopyLinearMap_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterHomotopyLinearMap R X 0 n c = 0 := rfl

theorem barycentricSubdivisionIterHomotopyLinearMap_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterHomotopyLinearMap R X (N+1) n c
      = barycentricSubdivisionIterHomotopyLinearMap R X N n c
        + barycentricSubdivisionIterLinearMap R X N (n+1)
            ((barycentricSubdivisionHomotopyLinearMap R X n).hom c) := rfl

/-- The degree-wise "`H ∘ ∂`" term of the iterated homotopy formula.  In degree
`0` it is `0`; in degree `m+1` it is `H^(N)_m (∂_m c)`.  This matches the project's
index convention `∂ : C_{n+1} → C_n = singularBoundary R X n`, exactly as
`homotopyBoundaryTerm` did for the one-step formula. -/
noncomputable def barycentricSubdivisionIterHomotopyBoundaryTerm
    (R : Type) [CommRing R] (X : TopCat.{0}) (N : ℕ) :
    (n : ℕ) → singularChainGroup R X n → singularChainGroup R X n
  | 0, _ => 0
  | (m+1), c => barycentricSubdivisionIterHomotopyLinearMap R X N m
      ((singularBoundary R X m).hom c)

theorem barycentricSubdivisionIterHomotopyBoundaryTerm_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) (N : ℕ) (c : singularChainGroup R X 0) :
    barycentricSubdivisionIterHomotopyBoundaryTerm R X N 0 c = 0 := rfl

theorem barycentricSubdivisionIterHomotopyBoundaryTerm_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (N m : ℕ) (c : singularChainGroup R X (m+1)) :
    barycentricSubdivisionIterHomotopyBoundaryTerm R X N (m+1) c
      = barycentricSubdivisionIterHomotopyLinearMap R X N m
          ((singularBoundary R X m).hom c) := rfl

/-- **Recursion for the boundary term.**  Increasing the iterate by one adds the
contribution `(sd^N)_n (H(∂ c))` from the one-step boundary term. -/
theorem barycentricSubdivisionIterHomotopyBoundaryTerm_succ_iter
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterHomotopyBoundaryTerm R X (N+1) n c
      = barycentricSubdivisionIterHomotopyBoundaryTerm R X N n c
        + barycentricSubdivisionIterLinearMap R X N n (homotopyBoundaryTerm R X n c) := by
  cases n with
  | zero =>
    simp [barycentricSubdivisionIterHomotopyBoundaryTerm, homotopyBoundaryTerm_zero]
  | succ m =>
    simp only [barycentricSubdivisionIterHomotopyBoundaryTerm_succ,
      barycentricSubdivisionIterHomotopyLinearMap_succ, homotopyBoundaryTerm_succ]

/-! ## 3. The chain homotopy `sd^N ≃ 𝟙` -/

/-- **Every iterate of barycentric subdivision is chain-homotopic to the
identity.** -/
noncomputable def barycentricSubdivisionIter_chainHomotopic_id
    (R : Type) [CommRing R] (X : TopCat.{0}) (N : ℕ) :
    Homotopy (barycentricSubdivisionIterChainMap R X N)
      (𝟙 (singularChainComplex R X)) := by
  induction N with
  | zero => exact Homotopy.refl _
  | succ N ih =>
    exact (Homotopy.comp (barycentricSubdivision_chainHomotopic_id R X) ih).trans
      (Homotopy.ofEq (Category.id_comp _))

/-- **`sd^N` induces the identity on homology.** -/
theorem barycentricSubdivisionIter_induces_identity_on_homology
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ) :
    HomologicalComplex.homologyMap (barycentricSubdivisionIterChainMap R X N) n
      = 𝟙 ((singularChainComplex R X).homology n) := by
  rw [(barycentricSubdivisionIter_chainHomotopic_id R X N).homologyMap_eq n,
    HomologicalComplex.homologyMap_id]

/-! ## 4. The explicit accumulated boundary formula -/

/-
**The iterated barycentric subdivision boundary formula.**

For every singular chain `c ∈ C_n(X; R)` and every `N`,
```text
c - sd^N(c) = ∂ (H^(N) c) + H^(N)(∂ c),
```
where `sd^N = barycentricSubdivisionIterLinearMap`, `H^(N) =
barycentricSubdivisionIterHomotopyLinearMap` is the explicit accumulated
homotopy, `∂ = singularBoundary`, and the term `H^(N)(∂ c)` is packaged degree-wise
as `barycentricSubdivisionIterHomotopyBoundaryTerm` (which is `H^(N)_{n-1}(∂_{n-1} c)`
in positive degree and `0` in degree `0`, matching the project's index convention
`∂ : C_{n+1} → C_n = singularBoundary R X n`).
-/
theorem barycentricSubdivisionIter_boundary_formula
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ)
    (c : singularChainGroup R X n) :
    c - barycentricSubdivisionIterLinearMap R X N n c
      = (singularBoundary R X n).hom
          (barycentricSubdivisionIterHomotopyLinearMap R X N n c)
        + barycentricSubdivisionIterHomotopyBoundaryTerm R X N n c := by
  induction' N with N ih generalizing n c;
  · simp +decide [ barycentricSubdivisionIterLinearMap_zero, barycentricSubdivisionIterHomotopyLinearMap_zero ];
    cases n <;> simp +decide [ barycentricSubdivisionIterHomotopyBoundaryTerm ];
  · have hlin : c - (barycentricSubdivisionIterLinearMap R X (N + 1) n) c = (c - (barycentricSubdivisionIterLinearMap R X N n) c) + (barycentricSubdivisionIterLinearMap R X N n) (c - (barycentricSubdivisionLinearMap R X n).hom c) := by
      simp +decide [ barycentricSubdivisionIterLinearMap_succ ];
    rw [ hlin, ih, barycentricSubdivisionIterHomotopyBoundaryTerm_succ_iter ];
    grind +suggestions

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
