import GroupApproximation.CharClass.OddPResolution
import GroupApproximation.CharClass.CartanDiagonalModule

/-!
# `W ⊗ C(X)` at odd `p`: the carrier and the differential

The source functor of both acyclic-models comparisons in this lane.  It is
`CartanDiagonalModule.lean`'s object with three changes and no fourth:

1. coefficients in `GroupRingZMod p` rather than `GroupRingZ2`;
2. the resolution half multiplies by `altCoeff (grS p) (grNorm p) i`, the scalar
   of the differential of `Wodd` **into** `W`-degree `i`, rather than by the
   single mod-2 scalar `1 + t`;
3. the simplicial half carries the Koszul sign `(-1)^i`, `i` the `W`-index of the
   source generator, which is invisible mod 2.

Everything else — the indexing, the two `Fin` eliminators, the reducibility of
the index type — is theirs, and the index type `WSIndex` is literally theirs:
it does not mention the coefficient ring, so redefining it here would be a
duplicate declaration in one namespace, which is the failure mode that only the
root build sees.

## Why the sign cannot be reindexed away

`d(e_i ⊗ σ) = d_W e_i ⊗ σ + (-1)^i (e_i ⊗ ∂σ)`.  Rescaling the resolution's
generators, `e_i ↦ ε_i e_i`, changes the resolution half's scalar by
`ε_i / ε_{i-1}` and leaves the simplicial half's sign exactly where it was,
because the same `i` occurs on both sides of that half.  So the sign is
intrinsic and is carried explicitly.  It is a *value*, never part of a type, so
it does not reintroduce the transports `CartanMidFour`'s post-mortem is about.

`d ∘ d = 0` is **not** proved here; it is the next file, exactly as
`CartanSourceComplex.lean` is the next file after `CartanDiagonalModule.lean`.
-/

open CategoryTheory Simplicial

namespace GroupApproximation.CharClass

/-- The singular boundary at odd `p`, abstractly, with **group-ring**
coefficients — the odd-primary twin of `SingularBoundaryData`.

Keeping the boundary abstract is what lets the source functor be built and
checked before the identification of the `Finsupp` presentation with Mathlib's
categorical-coproduct one is resolved.  Unlike the mod-2 structure, the
alternating signs of the faces are genuinely inside `bd` and are not collapsed;
`bd_bd` is the honest `∂∂ = 0`. -/
structure OddPBoundaryData (p : ℕ) where
  /-- The boundary `C_{n+1}(X) → C_n(X)` on the free `Λ`-module on simplices. -/
  bd : ∀ (X : TopCat.{0}) (n : ℕ),
    ((stdSimplexTop (n + 1) ⟶ X) →₀ GroupRingZMod p) →ₗ[GroupRingZMod p]
      ((stdSimplexTop n ⟶ X) →₀ GroupRingZMod p)
  /-- Naturality in the space. -/
  bd_natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
      (c : (stdSimplexTop (n + 1) ⟶ X) →₀ GroupRingZMod p),
      bd Y n (Finsupp.mapDomain (· ≫ f) c) = Finsupp.mapDomain (· ≫ f) (bd X n c)
  /-- `∂ ∘ ∂ = 0`. -/
  bd_bd : ∀ (X : TopCat.{0}) (n : ℕ) (c : (stdSimplexTop (n + 2) ⟶ X) →₀ GroupRingZMod p),
      bd X n (bd X (n + 1) c) = 0

/-- The underlying type of `(W ⊗ C(X))_k` at odd `p`: the free `Λ`-module on
`WSIndex`, the same index type the mod-2 construction uses. -/
abbrev OddWTensor (p k : ℕ) (X : TopCat.{0}) : Type := WSIndex k X →₀ GroupRingZMod p

/-- The resolution half of the differential on a generator: apply the
differential of `Wodd` to the `W`-factor, keeping the simplex.  Absent exactly
when the `W`-index is already `0`, the `Fin.last` branch.  The scalar is
`altCoeff` at the **target** `W`-degree `k - j`, which is what `altResolution_d`
delivers. -/
noncomputable def oddDiffW (p : ℕ) (X : TopCat.{0}) (k : ℕ) :
    ∀ n : Fin (k + 2), (stdSimplexTop n.val ⟶ X) → OddWTensor p k X :=
  Fin.lastCases (motive := fun n : Fin (k + 2) => (stdSimplexTop n.val ⟶ X) → OddWTensor p k X)
    (fun _ => 0)
    (fun j σ => altCoeff (grS p) (grNorm p) (k - j.val) •
      Finsupp.single (⟨j, σ⟩ : WSIndex k X) (1 : GroupRingZMod p))

@[simp] theorem oddDiffW_last (p : ℕ) (X : TopCat.{0}) (k : ℕ)
    (σ : stdSimplexTop (Fin.last (k + 1)).val ⟶ X) :
    oddDiffW p X k (Fin.last (k + 1)) σ = 0 := by
  rw [oddDiffW, Fin.lastCases_last]

@[simp] theorem oddDiffW_castSucc (p : ℕ) (X : TopCat.{0}) (k : ℕ) (j : Fin (k + 1))
    (σ : stdSimplexTop (Fin.castSucc j).val ⟶ X) :
    oddDiffW p X k (Fin.castSucc j) σ
      = altCoeff (grS p) (grNorm p) (k - j.val) •
          Finsupp.single (⟨j, σ⟩ : WSIndex k X) (1 : GroupRingZMod p) := by
  rw [oddDiffW, Fin.lastCases_castSucc]

/-- The simplicial half of the differential on a generator: the boundary of the
simplex, keeping the `W`-index, with the Koszul sign `(-1)^i` of the `W`-index
`i = k - m` of the source generator.  Absent exactly in simplex degree `0`, the
`Fin.cases` zero branch. -/
noncomputable def oddDiffS (p : ℕ) (data : OddPBoundaryData p) (X : TopCat.{0}) (k : ℕ) :
    ∀ n : Fin (k + 2), (stdSimplexTop n.val ⟶ X) → OddWTensor p k X :=
  Fin.cases (motive := fun n : Fin (k + 2) => (stdSimplexTop n.val ⟶ X) → OddWTensor p k X)
    (fun _ => 0)
    (fun m σ => ((-1 : GroupRingZMod p) ^ (k - m.val)) •
      Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
        (fun τ => (⟨m, τ⟩ : WSIndex k X))
        (data.bd X m.val (Finsupp.single σ (1 : GroupRingZMod p))))

@[simp] theorem oddDiffS_zero (p : ℕ) (data : OddPBoundaryData p) (X : TopCat.{0}) (k : ℕ)
    (σ : stdSimplexTop (0 : Fin (k + 2)).val ⟶ X) : oddDiffS p data X k 0 σ = 0 := by
  rw [oddDiffS, Fin.cases_zero]

@[simp] theorem oddDiffS_succ (p : ℕ) (data : OddPBoundaryData p) (X : TopCat.{0}) (k : ℕ)
    (m : Fin (k + 1)) (σ : stdSimplexTop (Fin.succ m).val ⟶ X) :
    oddDiffS p data X k (Fin.succ m) σ
      = ((-1 : GroupRingZMod p) ^ (k - m.val)) •
          Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p)
            (fun τ => (⟨m, τ⟩ : WSIndex k X))
            (data.bd X m.val (Finsupp.single σ (1 : GroupRingZMod p))) := by
  rw [oddDiffS, Fin.cases_succ]

/-- The value of the differential on one generator `e_{k+1-n} ⊗ σ` of degree
`k + 1`. -/
noncomputable def oddDiffGen (p : ℕ) (data : OddPBoundaryData p) (X : TopCat.{0}) (k : ℕ)
    (n : Fin (k + 2)) (σ : stdSimplexTop n.val ⟶ X) : OddWTensor p k X :=
  oddDiffW p X k n σ + oddDiffS p data X k n σ

/-- **The differential of `W ⊗ C(X)`**, as a `Λ`-linear map. -/
noncomputable def oddDiff (p : ℕ) (data : OddPBoundaryData p) (X : TopCat.{0}) (k : ℕ) :
    OddWTensor p (k + 1) X →ₗ[GroupRingZMod p] OddWTensor p k X :=
  Finsupp.linearCombination (GroupRingZMod p)
    (fun q : WSIndex (k + 1) X => oddDiffGen p data X k q.1 q.2)

@[simp] theorem oddDiff_single (p : ℕ) (data : OddPBoundaryData p) (X : TopCat.{0}) (k : ℕ)
    (q : WSIndex (k + 1) X) :
    oddDiff p data X k (Finsupp.single q (1 : GroupRingZMod p))
      = oddDiffGen p data X k q.1 q.2 := by
  rw [oddDiff, Finsupp.linearCombination_single, one_smul]

end GroupApproximation.CharClass
