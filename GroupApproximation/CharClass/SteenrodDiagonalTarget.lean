import GroupApproximation.CharClass.SteenrodDiagonalLambda

/-!
# The target complex `S(X) ⊗ S(X)`, and its differential

`cc-cartan`'s "index one degree, derive the other" convention is right for the
source `W ⊗ S(X)`, because each half of its differential leaves one of the two
data pieces untouched.  It is **wrong for the target**: there both factors are
data, each half of `∂ ⊗ 1 + 1 ⊗ ∂` moves one of them, and the other factor's
declared degree is a derived subtraction.  Since `Nat.sub` recurses on its second
argument, `(k+1) - j` and `(k - j) + 1` are equal only propositionally, so that
convention forces a transport of a *simplex* along an equality of degrees — a
dependent proof argument inside a definition, which blocks every later rewrite.

So the target is indexed by **both** degrees, with the sum constraint carried as
a proposition:

```text
PairDeg k     = {p : ℕ × ℕ // p.1 + p.2 = k}
PairIdx X k   = Σ p : PairDeg k, (a p.1.1-simplex) × (a p.1.2-simplex)
```

Now each half of the differential moves only a proof of a `ℕ` equation, which is
proof-irrelevant, and no data is transported at all.  Both halves are cast-free,
which is the property `cc-cartan` rightly insisted on for the source.

The published `PairIndex` of `SteenrodDiagonalLambda.lean` is kept and bridged
(`pairIndexToIdx`) rather than changed, per the fleet rule on frozen signatures.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. The carrier -/

/-- A pair of degrees summing to `k`, the constraint carried as a proposition. -/
def PairDeg (k : ℕ) : Type := {p : ℕ × ℕ // p.1 + p.2 = k}

@[ext] theorem PairDeg.ext {k : ℕ} {p q : PairDeg k} (h : p.val = q.val) : p = q :=
  Subtype.ext h

/-- The basis of `(S(X) ⊗ S(X))_k`: a pair of simplices of degrees summing to
`k`. -/
def PairIdx (X : TopCat.{0}) (k : ℕ) : Type :=
  Σ p : PairDeg k, singularSimplices X p.val.1 × singularSimplices X p.val.2

/-- The bidegree `(a, k - a)`. -/
def pairDegOf (k : ℕ) (a : Fin (k + 1)) : PairDeg k :=
  ⟨(a.val, k - a.val), by omega⟩

/-- **The bridge from the published carrier.**  `PairIndex` indexes by the first
degree and derives the second; `PairIdx` carries both.  On the nose the data is
the same, so the bridge is definitional. -/
def pairIndexToIdx (X : TopCat.{0}) (k : ℕ) (p : PairIndex X k) : PairIdx X k :=
  ⟨pairDegOf k p.1, p.2⟩

/-! ## 2. The two halves of the differential -/

/-- `∂ ⊗ 1`: the boundary of the left factor, the right factor untouched.  The
match on the left degree is what keeps it cast-free: in the successor branch the
simplex already has the degree the face map wants. -/
noncomputable def dLeft (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k : ℕ) :
    ∀ (a b : ℕ), a + b = k + 1 → singularSimplices X a → singularSimplices X b →
      (PairIdx X k →₀ Λ)
  | 0, _, _, _, _ => 0
  | a' + 1, b, h, σ, τ =>
      ∑ j : Fin (a' + 2),
        Finsupp.single
          (⟨⟨(a', b), by omega⟩, (faceSimplex X a' j σ, τ)⟩ : PairIdx X k) 1

/-- `1 ⊗ ∂`: the boundary of the right factor, the left factor untouched. -/
noncomputable def dRight (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k : ℕ) :
    ∀ (a b : ℕ), a + b = k + 1 → singularSimplices X a → singularSimplices X b →
      (PairIdx X k →₀ Λ)
  | _, 0, _, _, _ => 0
  | a, b' + 1, h, σ, τ =>
      ∑ j : Fin (b' + 2),
        Finsupp.single
          (⟨⟨(a, b'), by omega⟩, (σ, faceSimplex X b' j τ)⟩ : PairIdx X k) 1

@[simp] theorem dLeft_zero (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k b : ℕ)
    (h : 0 + b = k + 1) (σ : singularSimplices X 0) (τ : singularSimplices X b) :
    dLeft X Λ k 0 b h σ τ = 0 := rfl

@[simp] theorem dRight_zero (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k a : ℕ)
    (h : a + 0 = k + 1) (σ : singularSimplices X a) (τ : singularSimplices X 0) :
    dRight X Λ k a 0 h σ τ = 0 := rfl

theorem dLeft_succ (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k a' b : ℕ)
    (h : a' + 1 + b = k + 1) (σ : singularSimplices X (a' + 1))
    (τ : singularSimplices X b) :
    dLeft X Λ k (a' + 1) b h σ τ
      = ∑ j : Fin (a' + 2),
          Finsupp.single
            (⟨⟨(a', b), by omega⟩, (faceSimplex X a' j σ, τ)⟩ : PairIdx X k) 1 := rfl

theorem dRight_succ (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k a b' : ℕ)
    (h : a + (b' + 1) = k + 1) (σ : singularSimplices X a)
    (τ : singularSimplices X (b' + 1)) :
    dRight X Λ k a (b' + 1) h σ τ
      = ∑ j : Fin (b' + 2),
          Finsupp.single
            (⟨⟨(a, b'), by omega⟩, (σ, faceSimplex X b' j τ)⟩ : PairIdx X k) 1 := rfl

/-! ## 3. The differential -/

/-- The differential on a basis element. -/
noncomputable def dGen (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k : ℕ)
    (q : PairIdx X (k + 1)) : PairIdx X k →₀ Λ :=
  dLeft X Λ k q.1.val.1 q.1.val.2 q.1.property q.2.1 q.2.2
    + dRight X Λ k q.1.val.1 q.1.val.2 q.1.property q.2.1 q.2.2

/-- **The differential of `S(X) ⊗ S(X)`**, as a `Λ`-linear map. -/
noncomputable def dTgt (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k : ℕ) :
    (PairIdx X (k + 1) →₀ Λ) →ₗ[Λ] (PairIdx X k →₀ Λ) :=
  Finsupp.linearCombination Λ (dGen X Λ k)

@[simp] theorem dTgt_single (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k : ℕ)
    (q : PairIdx X (k + 1)) (c : Λ) :
    dTgt X Λ k (Finsupp.single q c) = c • dGen X Λ k q := by
  unfold dTgt
  simp

theorem dTgt_single_one (X : TopCat.{0}) (Λ : Type) [CommRing Λ] (k : ℕ)
    (q : PairIdx X (k + 1)) :
    dTgt X Λ k (Finsupp.single q 1) = dGen X Λ k q := by
  rw [dTgt_single, one_smul]

end

end Steenrod
end CharClass
end GroupApproximation
