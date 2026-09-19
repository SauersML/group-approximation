import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# The commutant does not separate `A₄ < S₄`

This file formalizes a counterexample that `non_mf_groups_exist.tex` used to
print inside an invariant-size remark:

> The natural candidate size, the dimension `dim_k End_H(V)` of the commutant,
> is order-reversing rather than order-preserving, and it does not separate
> nested subgroups: `A₄ < S₄` in the standard three-dimensional representation
> have the same commutant `k·1`.

**That remark is no longer in the manuscript.**  It was cut in the pass that
landed as `e6d76e07`, so `rem:invariantsize` is not a `\label` any more and the
quotation above is a record rather than a citation.  Legacy ledger row `FD.20`.
Line numbers are deliberately not cited: the manuscript is under concurrent
edit.

Two assertions are made there and both are proved below.

* **Order-reversing.**  `commutant_antitone`: a larger subgroup has a smaller
  commutant.  This is stated for an arbitrary matrix representation of an
  arbitrary group, since that is the generality in which the manuscript makes
  the remark.
* **Does not separate.**  `commutant_top_eq_commutant_alternatingGroup` and
  `commutant_alternatingGroup`: in the standard three-dimensional
  representation the commutant of `A₄` and the commutant of `S₄` are both the
  scalars `k ∙ 1`, while `alternatingGroup_lt_top` records that `A₄ < S₄`
  really is strict.  `finrank_commutant_alternatingGroup` reads the common
  value off as `dim_k = 1`, which is the number the manuscript's candidate size
  assigns to both subgroups.

`commutant_does_not_separate` bundles the four statements, and
`standardRep_commutant_does_not_separate_complex` is the `ℂ` specialization.

## Why this file carries no badge

**The absence of a `\leanverified` citation here is deliberate, not an
oversight.**  While the remark was in print it contained exactly one badge
slot, belonging to the invariant-size principle of its *first* paragraph
(`manuscriptInvariantSizePrinciple`, ledger rows `FD.18`/`FD.19`); the
`A₄ < S₄` sentence was in the second paragraph and had no slot of its own.
Now that the remark is gone there is no printed sentence left to badge at all,
so the terminal state of `FD.20` is **formalized, with no printed claim to
attach to**.  The theorems below are correct and are in the root import
closure; they simply no longer correspond to anything the reader sees, and a
badge must not be invented for them.

## Characteristic

The manuscript writes `k` for an unspecified field, and everything below
instead carries the hypothesis `(2 : k) ≠ 0`.  **This is a limitation of the
construction, not of the statement.**  In characteristic `2` the three columns
`v₁, v₂, v₃` of `basisMatrix` all collapse to the all-ones vector, so that
matrix stops being a basis of the sum-zero subspace and `coordMatrix` stops
being a left inverse of it; the compression below then degenerates and proves
nothing.  Characteristic `3` is fine, even though `A₄` has order divisible
by `3`.

The printed claim itself does survive in characteristic `2` — over `𝔽₂` the
commutant of `A₄` on the sum-zero subspace of `𝔽₂⁴` is still one-dimensional,
even though that subspace now contains the all-ones vector and the
representation is no longer semisimple; the three Jordan--Hölder factors are
pairwise non-isomorphic, which is what keeps the commutant scalar.  That case
needs a different argument and is **not** formalized here.

## The construction

`Mathlib` has no standard representation of `Sₙ`, so one is built here.  The
cheap route is *not* to build it directly but to cut it out of the permutation
representation on `k⁴`, which `Mathlib` does have as
`Matrix.permMatrixHom : Equiv.Perm n →* Matrix n n k`.

Use `permMatrixHom`, never `Equiv.Perm.permMatrix` directly: the latter is
**anti**-multiplicative, `(σ * τ).permMatrix = τ.permMatrix * σ.permMatrix`
(`Matrix.permMatrix_mul`), because `PEquiv.toMatrix` turns composition around.
`permMatrixHom` is the repaired version, `σ ↦ σ⁻¹.permMatrix`, and it is a
genuine `MonoidHom`.  That one fact is what makes the whole construction below
case-free: `std` inherits multiplicativity from `P` instead of having to be
checked on the 24 elements of `S₄`.  Building the representation by hand and
verifying `std (g h) = std g · std h` elementwise is the expensive route that
this avoids.

Let `J` be the all-ones `4×4` matrix (`allOnes`) and let `T` (`basisMatrix`) be
the `4×3` matrix whose three columns are

```
v₁ = ( 1,  1, -1, -1)
v₂ = ( 1, -1,  1, -1)
v₃ = ( 1, -1, -1,  1)
```

a basis of the sum-zero subspace of `k⁴`.  Put `S := (4:k)⁻¹ • Tᵀ`
(`coordMatrix`), and define the standard representation by compressing:

```
std g := S * P g * T,      P := Matrix.permMatrixHom.
```

Multiplicativity is then **free**, with no case check over the 24 elements of
`S₄`.  The four inputs are all single computations with `±1` entries:

* `Tᵀ T = 4·1₃`, hence `S T = 1₃`;
* `T Tᵀ = 4·1₄ - J`, hence `T S = 1₄ - (4:k)⁻¹ • J`;
* `J T = 0` and `Tᵀ J = 0` — this is precisely the statement that the columns
  of `T` sum to zero, i.e. that they lie in the standard summand;
* `P g * J = J = J * P g`, because a permutation matrix has all row sums and
  all column sums equal to `1`.

The first consequence is the intertwining relation `P g * T = T * std g`
(`permMatrixHom_mul_basisMatrix`):

```
T * std g = (T S) (P g) T = (1 - c J)(P g) T = (P g) T - c (J (P g) T)
          = (P g) T - c (J T) = (P g) T,          c := (4:k)⁻¹,
```

using `J * P g = J` and `J T = 0`.  Multiplicativity follows from it at once,
since `P` is a homomorphism:

```
P (g h) T = P g (P h T) = P g (T (std h)) = (P g T)(std h)
          = T (std g)(std h),
```

and `stdFun_eq_of_intertwines` converts that back into `std (g h) = std g std h`.
The same relation is what lets the three generator matrices be read off by a
`4×3` computation with integer entries only, with no `(4:k)⁻¹` in sight.

Faithfulness (`stdHom_injective`) is likewise free of case analysis:
`J + T Tᵀ = 4·1₄`, so a `g` with `P g * T = T` satisfies `P g * (4·1) = 4·1`.

## The commutant computation

Write `σ = (0 1)(2 3)`, `τ = (0 2)(1 3)` and `c = (0 1 2)`, all in `A₄`
(`gen1`, `gen2`, `gen3`).  In the basis `v₁, v₂, v₃` the manuscript's four-line
computation reads:

```
std σ = diag( 1, -1, -1)          std τ = diag(-1,  1, -1)

           ⎡ 0  1  0⎤
std c =    ⎢ 0  0 -1⎥            (c : v₁ ↦ -v₃, v₂ ↦ v₁, v₃ ↦ -v₂)
           ⎣-1  0  0⎦
```

Let `M` commute with all three.  Commuting with a diagonal matrix `D` gives
`(D_jj - D_ii)·M_ij = 0` for every entry.  From `std σ` the differences at the
entries `(0,1), (0,2), (1,0), (2,0)` are `∓2`, so — and this is the only place
`(2 : k) ≠ 0` is used — those four entries vanish; from `std τ` the same
argument at `(1,2)` and `(2,1)` kills the remaining two.  So `M` is diagonal.
Now commuting with `std c` gives `(M_ii - M_jj)·(std c)_ij = 0`, and the
entries `(0,1)` and `(1,2)` of `std c` are units, so `M₀₀ = M₁₁ = M₂₂` and `M`
is scalar.  Hence `End_{A₄}(V) = k·1`.

The `S₄` side is then pure formality and needs no further computation: by
`commutant_antitone`,

```
k·1 ⊆ End_{S₄}(V) ⊆ End_{A₄}(V) = k·1,
```

which is the manuscript's point — the candidate size takes the same value `1`
on the strictly smaller subgroup, so it cannot separate them.
-/

namespace GroupApproximation
namespace StandardRepCommutant

open Equiv

-- `ᵀ` is *scoped* notation for `Matrix.transpose`
-- (`Mathlib/LinearAlgebra/Matrix/Defs.lean:157`, `scoped postfix:1024 "ᵀ"`), so it
-- is a parse error without this line even though every declaration below is
-- written out with its full `Matrix.` prefix.
open scoped Matrix

/-! ## Order-reversal, in the generality the manuscript states it -/

/-- **The commutant is order-reversing.**  For any representation of any group
by matrices, enlarging the subgroup shrinks its commutant.  This is the first
half of the manuscript's sentence: the candidate size `dim_k End_H(V)` is
antitone in `H`, not monotone. -/
theorem commutant_antitone {G : Type*} [Group G] {n : Type*} {R : Type*}
    [Fintype n] [CommRing R] (ρ : G → Matrix n n R)
    {H H' : Subgroup G} (hHH' : H ≤ H') :
    {M : Matrix n n R | ∀ g ∈ H', M * ρ g = ρ g * M}
      ⊆ {M : Matrix n n R | ∀ g ∈ H, M * ρ g = ρ g * M} :=
  fun _ hM g hg => hM g (hHH' hg)

/-! ## The three matrices of the construction -/

variable (k : Type*) [Field k]

/-- The all-ones `4×4` matrix `J`. -/
def allOnes : Matrix (Fin 4) (Fin 4) k := Matrix.of fun _ _ => 1

/-- `T`: the `4×3` matrix whose columns are the basis `v₁, v₂, v₃` of the
sum-zero subspace of `k⁴` used throughout.  Its rows are the four characters of
the Klein four-group, which is why the two Klein involutions of `A₄` act
diagonally in this basis. -/
def basisMatrix : Matrix (Fin 4) (Fin 3) k :=
  !![1, 1, 1; 1, -1, -1; -1, 1, -1; -1, -1, 1]

/-- `S`: the left inverse `(4:k)⁻¹ • Tᵀ` of `T`.  In characteristic `2` this is
the zero matrix and nothing below applies; every statement that needs it to be
a genuine left inverse carries `(2 : k) ≠ 0`. -/
def coordMatrix : Matrix (Fin 3) (Fin 4) k := (4 : k)⁻¹ • (basisMatrix k)ᵀ

/-- `(2 : k) ≠ 0` upgrades to `(4 : k) ≠ 0`. -/
theorem four_ne_zero (h2 : (2 : k) ≠ 0) : (4 : k) ≠ 0 := by
  intro h
  have hmul : (2 : k) * 2 = 0 := by linear_combination h
  rcases mul_eq_zero.mp hmul with h' | h' <;> exact h2 h'

/-- In characteristic `≠ 2`, a doubled element vanishes only if it does. -/
theorem eq_zero_of_two_mul_eq_zero (h2 : (2 : k) ≠ 0) {x : k}
    (h : (2 : k) * x = 0) : x = 0 :=
  (mul_eq_zero.mp h).resolve_left h2

/-! ### The four `±1` identities

These are the only computations in the file with a fixed numeric matrix on both
sides; everything else is derived from them formally. -/

/-- `Tᵀ T = 4·1₃`: the three columns of `T` are pairwise orthogonal of square
length `4`. -/
theorem transpose_basisMatrix_mul_basisMatrix :
    (basisMatrix k)ᵀ * basisMatrix k = (4 : k) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [basisMatrix, Matrix.mul_apply, Fin.sum_univ_four]; try ring)

/-- `T Tᵀ = 4·1₄ - J`: the complementary statement, saying that
`(4:k)⁻¹ • T Tᵀ` is the projection onto the standard summand along the
all-ones vector. -/
theorem basisMatrix_mul_transpose_basisMatrix :
    basisMatrix k * (basisMatrix k)ᵀ = (4 : k) • 1 - allOnes k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [basisMatrix, allOnes, Matrix.mul_apply, Fin.sum_univ_three]; try ring)

/-- `J T = 0`: the columns of `T` sum to zero, i.e. they lie in the standard
summand.  This is the identity that makes the compression multiplicative. -/
theorem allOnes_mul_basisMatrix : allOnes k * basisMatrix k = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [basisMatrix, allOnes, Matrix.mul_apply, Fin.sum_univ_four]; try ring)

/-- `Tᵀ J = 0`, the transposed form of `allOnes_mul_basisMatrix`. -/
theorem transpose_basisMatrix_mul_allOnes : (basisMatrix k)ᵀ * allOnes k = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [basisMatrix, allOnes, Matrix.mul_apply, Fin.sum_univ_four]; try ring)

/-! ### Consequences for `S` -/

/-- `S T = 1₃`. -/
theorem coordMatrix_mul_basisMatrix (h2 : (2 : k) ≠ 0) :
    coordMatrix k * basisMatrix k = 1 := by
  rw [coordMatrix, Matrix.smul_mul, transpose_basisMatrix_mul_basisMatrix,
    smul_smul, inv_mul_cancel₀ (four_ne_zero k h2), one_smul]

/-- `T S = 1₄ - (4:k)⁻¹ • J`, the projection onto the standard summand. -/
theorem basisMatrix_mul_coordMatrix (h2 : (2 : k) ≠ 0) :
    basisMatrix k * coordMatrix k = 1 - (4 : k)⁻¹ • allOnes k := by
  rw [coordMatrix, Matrix.mul_smul, basisMatrix_mul_transpose_basisMatrix,
    smul_sub, smul_smul, inv_mul_cancel₀ (four_ne_zero k h2), one_smul]

/-- `S J = 0`. -/
theorem coordMatrix_mul_allOnes : coordMatrix k * allOnes k = 0 := by
  rw [coordMatrix, Matrix.smul_mul, transpose_basisMatrix_mul_allOnes, smul_zero]

/-! ### Permutation matrices absorb the all-ones matrix -/

/-- Reading an entry of `P g * M`: the permutation matrix relabels rows. -/
theorem permMatrixHom_mul_apply (g : Equiv.Perm (Fin 4))
    (M : Matrix (Fin 4) (Fin 3) k) (i : Fin 4) (j : Fin 3) :
    ((Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * M) i j = M (g⁻¹ i) j := by
  have h : (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * M
      = M.submatrix (g⁻¹ : Equiv.Perm (Fin 4)) id :=
    PEquiv.toMatrix_toPEquiv_mul (g⁻¹ : Equiv.Perm (Fin 4)) M
  rw [h]
  rfl

/-- `P g * J = J`: every row sum of a permutation matrix is `1`. -/
theorem permMatrixHom_mul_allOnes (g : Equiv.Perm (Fin 4)) :
    (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * allOnes k = allOnes k := by
  have h : (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * allOnes k
      = (allOnes k).submatrix (g⁻¹ : Equiv.Perm (Fin 4)) id :=
    PEquiv.toMatrix_toPEquiv_mul (g⁻¹ : Equiv.Perm (Fin 4)) (allOnes k)
  rw [h]
  rfl

/-- `J * P g = J`: every column sum of a permutation matrix is `1`. -/
theorem allOnes_mul_permMatrixHom (g : Equiv.Perm (Fin 4)) :
    allOnes k * (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) = allOnes k := by
  have h : allOnes k * (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k)
      = (allOnes k).submatrix id (g⁻¹ : Equiv.Perm (Fin 4)).symm :=
    PEquiv.mul_toMatrix_toPEquiv (allOnes k) (g⁻¹ : Equiv.Perm (Fin 4))
  rw [h]
  rfl

/-! ## The standard three-dimensional representation -/

/-- The standard representation as a bare function, `std g = S · P g · T`.
Keeping it separate from the bundled `stdHom` means the matrix computations
below carry no proof argument. -/
def stdFun (g : Equiv.Perm (Fin 4)) : Matrix (Fin 3) (Fin 3) k :=
  coordMatrix k * (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * basisMatrix k

/-- **The intertwining relation `P g · T = T · std g`.**  It says that `T`
identifies `k³` with the standard summand of `k⁴` equivariantly.  Everything
else about `std` — multiplicativity, faithfulness, and the three generator
matrices — is derived from this one identity. -/
theorem permMatrixHom_mul_basisMatrix (h2 : (2 : k) ≠ 0) (g : Equiv.Perm (Fin 4)) :
    (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * basisMatrix k
      = basisMatrix k * stdFun k g := by
  symm
  calc basisMatrix k * stdFun k g
      = (basisMatrix k * coordMatrix k)
          * ((Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * basisMatrix k) := by
        simp only [stdFun, Matrix.mul_assoc]
    _ = (1 - (4 : k)⁻¹ • allOnes k)
          * ((Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * basisMatrix k) := by
        rw [basisMatrix_mul_coordMatrix k h2]
    _ = (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * basisMatrix k
          - (4 : k)⁻¹ • (allOnes k
              * ((Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k)
                * basisMatrix k)) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    _ = (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * basisMatrix k := by
        rw [← Matrix.mul_assoc, allOnes_mul_permMatrixHom, allOnes_mul_basisMatrix,
          smul_zero, sub_zero]

/-- **Reading off a value of `std`.**  If `P g` moves the columns of `T` by the
explicit matrix `D`, then `std g` *is* `D`.  Every generator matrix below is
obtained this way, from a `4×3` identity with entries `0, ±1`. -/
theorem stdFun_eq_of_intertwines (h2 : (2 : k) ≠ 0) (g : Equiv.Perm (Fin 4))
    (D : Matrix (Fin 3) (Fin 3) k)
    (h : (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * basisMatrix k
      = basisMatrix k * D) :
    stdFun k g = D := by
  show coordMatrix k * (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k)
      * basisMatrix k = D
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, coordMatrix_mul_basisMatrix k h2,
    Matrix.one_mul]

/-- `std 1 = 1`. -/
theorem stdFun_one (h2 : (2 : k) ≠ 0) : stdFun k 1 = 1 := by
  show coordMatrix k * (Matrix.permMatrixHom (1 : Equiv.Perm (Fin 4))
      : Matrix (Fin 4) (Fin 4) k) * basisMatrix k = 1
  rw [map_one, Matrix.mul_one, coordMatrix_mul_basisMatrix k h2]

/-- `std` is multiplicative.  No case analysis over `S₄` occurs: the whole
content is that `P` is a homomorphism and that `T` intertwines. -/
theorem stdFun_mul (h2 : (2 : k) ≠ 0) (g h : Equiv.Perm (Fin 4)) :
    stdFun k (g * h) = stdFun k g * stdFun k h := by
  refine stdFun_eq_of_intertwines k h2 _ _ ?_
  rw [map_mul]
  calc (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k)
        * (Matrix.permMatrixHom h : Matrix (Fin 4) (Fin 4) k) * basisMatrix k
      = (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k)
          * ((Matrix.permMatrixHom h : Matrix (Fin 4) (Fin 4) k) * basisMatrix k) :=
        Matrix.mul_assoc _ _ _
    _ = (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k)
          * (basisMatrix k * stdFun k h) := by
        rw [permMatrixHom_mul_basisMatrix k h2]
    _ = ((Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * basisMatrix k)
          * stdFun k h := (Matrix.mul_assoc _ _ _).symm
    _ = (basisMatrix k * stdFun k g) * stdFun k h := by
        rw [permMatrixHom_mul_basisMatrix k h2]
    _ = basisMatrix k * (stdFun k g * stdFun k h) := Matrix.mul_assoc _ _ _

/-- **The standard three-dimensional representation of `S₄`.**  `Mathlib` has
no standard representation of `Sₙ`, so this is it: the compression of the
permutation representation on `k⁴` to the sum-zero summand, in the basis
`v₁, v₂, v₃`. -/
def stdHom (h2 : (2 : k) ≠ 0) : Equiv.Perm (Fin 4) →* Matrix (Fin 3) (Fin 3) k where
  toFun := stdFun k
  map_one' := stdFun_one k h2
  map_mul' := stdFun_mul k h2

@[simp]
theorem stdHom_apply (h2 : (2 : k) ≠ 0) (g : Equiv.Perm (Fin 4)) :
    stdHom k h2 g = stdFun k g := rfl

/-! ### Faithfulness -/

/-- A permutation matrix is the identity matrix with its rows relabelled.

This goes through `PEquiv.toMatrix_toPEquiv_mul` rather than the more direct
`PEquiv.toMatrix_toPEquiv_apply`, because the latter mentions its scalar type
only in its conclusion, so `k` would have to be recovered from the expected
type; here the explicit `(1 : Matrix (Fin 4) (Fin 4) k)` argument pins it. -/
theorem permMatrixHom_eq_submatrix (g : Equiv.Perm (Fin 4)) :
    (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k)
      = (1 : Matrix (Fin 4) (Fin 4) k).submatrix (g⁻¹ : Equiv.Perm (Fin 4)) id := by
  have h := PEquiv.toMatrix_toPEquiv_mul (g⁻¹ : Equiv.Perm (Fin 4))
    (1 : Matrix (Fin 4) (Fin 4) k)
  rwa [Matrix.mul_one] at h

/-- A permutation whose matrix is the identity is the identity. -/
theorem eq_one_of_permMatrixHom_eq_one {g : Equiv.Perm (Fin 4)}
    (h : (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) = 1) : g = 1 := by
  have key : ∀ i : Fin 4, g⁻¹ i = i := by
    intro i
    by_contra hne
    have hone : ((Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k)) i i = 1 := by
      rw [h, Matrix.one_apply_eq]
    rw [permMatrixHom_eq_submatrix k g] at hone
    -- `submatrix` and `id` both unfold definitionally, so this is a retype.
    have hzero : (1 : Matrix (Fin 4) (Fin 4) k) (g⁻¹ i) i = 1 := hone
    rw [Matrix.one_apply_ne hne] at hzero
    exact zero_ne_one hzero
  have hinv : g⁻¹ = 1 := Equiv.ext key
  exact inv_eq_one.mp hinv

/-- **`std` is faithful.**  If `std g = 1` then `P g` fixes the columns of `T`,
and it fixes the all-ones vector for free; since `J + T Tᵀ = 4·1₄` and
`(4 : k) ≠ 0`, this forces `P g = 1`. -/
theorem stdHom_injective (h2 : (2 : k) ≠ 0) : Function.Injective (stdHom k h2) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hT : (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * basisMatrix k
      = basisMatrix k := by
    rw [permMatrixHom_mul_basisMatrix k h2 g, show stdFun k g = 1 from hg,
      Matrix.mul_one]
  have hsum : allOnes k + basisMatrix k * (basisMatrix k)ᵀ = (4 : k) • 1 := by
    rw [basisMatrix_mul_transpose_basisMatrix]
    abel
  have hP : (Matrix.permMatrixHom g : Matrix (Fin 4) (Fin 4) k) * ((4 : k) • 1)
      = (4 : k) • 1 := by
    rw [← hsum, Matrix.mul_add, permMatrixHom_mul_allOnes, ← Matrix.mul_assoc, hT]
  rw [Matrix.mul_smul, Matrix.mul_one] at hP
  have hscale := congrArg (fun N : Matrix (Fin 4) (Fin 4) k => (4 : k)⁻¹ • N) hP
  simp only [smul_smul, inv_mul_cancel₀ (four_ne_zero k h2), one_smul] at hscale
  exact eq_one_of_permMatrixHom_eq_one k hscale

/-! ## The three generators of `A₄` and their matrices -/

/-- The Klein involution `(0 1)(2 3)`. -/
def gen1 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The Klein involution `(0 2)(1 3)`. -/
def gen2 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- The three-cycle `(0 1 2)`, i.e. `0 ↦ 1 ↦ 2 ↦ 0`. -/
def gen3 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 0 1

theorem gen1_mem : gen1 ∈ alternatingGroup (Fin 4) := by
  have ha : (0 : Fin 4) ≠ 1 := by decide
  have hb : (2 : Fin 4) ≠ 3 := by decide
  simp [Equiv.Perm.mem_alternatingGroup, gen1, Equiv.Perm.sign_swap ha,
    Equiv.Perm.sign_swap hb]

theorem gen2_mem : gen2 ∈ alternatingGroup (Fin 4) := by
  have ha : (0 : Fin 4) ≠ 2 := by decide
  have hb : (1 : Fin 4) ≠ 3 := by decide
  simp [Equiv.Perm.mem_alternatingGroup, gen2, Equiv.Perm.sign_swap ha,
    Equiv.Perm.sign_swap hb]

theorem gen3_mem : gen3 ∈ alternatingGroup (Fin 4) := by
  have ha : (0 : Fin 4) ≠ 2 := by decide
  have hb : (0 : Fin 4) ≠ 1 := by decide
  simp [Equiv.Perm.mem_alternatingGroup, gen3, Equiv.Perm.sign_swap ha,
    Equiv.Perm.sign_swap hb]

/-- `A₄` is a *proper* subgroup of `S₄`: a transposition is missing.  This is
what makes the commutant's failure to separate a genuine failure. -/
theorem alternatingGroup_lt_top : alternatingGroup (Fin 4) < ⊤ := by
  refine lt_of_le_of_ne le_top ?_
  intro hEq
  have hmem : Equiv.swap (0 : Fin 4) 1 ∈ alternatingGroup (Fin 4) := by
    rw [hEq]; exact Subgroup.mem_top _
  rw [Equiv.Perm.mem_alternatingGroup,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)] at hmem
  exact absurd hmem (by decide)

/-- `std (0 1)(2 3) = diag(1, -1, -1)`. -/
def d1 : Matrix (Fin 3) (Fin 3) k := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

/-- `std (0 2)(1 3) = diag(-1, 1, -1)`. -/
def d2 : Matrix (Fin 3) (Fin 3) k := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- `std (0 1 2)`, sending `v₁ ↦ -v₃`, `v₂ ↦ v₁`, `v₃ ↦ -v₂`. -/
def d3 : Matrix (Fin 3) (Fin 3) k := !![0, 1, 0; 0, 0, -1; -1, 0, 0]

theorem stdFun_gen1 (h2 : (2 : k) ≠ 0) : stdFun k gen1 = d1 k := by
  refine stdFun_eq_of_intertwines k h2 _ _ ?_
  have hinv : (gen1)⁻¹ = gen1 := by apply Equiv.ext; decide
  ext i j
  rw [permMatrixHom_mul_apply, hinv]
  fin_cases i <;> fin_cases j <;>
    (simp [gen1, d1, basisMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]; try ring)

theorem stdFun_gen2 (h2 : (2 : k) ≠ 0) : stdFun k gen2 = d2 k := by
  refine stdFun_eq_of_intertwines k h2 _ _ ?_
  have hinv : (gen2)⁻¹ = gen2 := by apply Equiv.ext; decide
  ext i j
  rw [permMatrixHom_mul_apply, hinv]
  fin_cases i <;> fin_cases j <;>
    (simp [gen2, d2, basisMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]; try ring)

theorem stdFun_gen3 (h2 : (2 : k) ≠ 0) : stdFun k gen3 = d3 k := by
  refine stdFun_eq_of_intertwines k h2 _ _ ?_
  have hinv : (gen3)⁻¹ = Equiv.swap 0 1 * Equiv.swap 0 2 := by
    apply Equiv.ext; decide
  ext i j
  rw [permMatrixHom_mul_apply, hinv]
  fin_cases i <;> fin_cases j <;>
    (simp [d3, basisMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]; try ring)

/-! ## The commutant -/

/-- The commutant of the image of a subgroup `H ≤ S₄` in the standard
representation, as a `k`-submodule of `M₃(k)`.  This is the manuscript's
`End_H(V)`. -/
def commutant (H : Subgroup (Equiv.Perm (Fin 4))) :
    Submodule k (Matrix (Fin 3) (Fin 3) k) where
  carrier := {M | ∀ g ∈ H, M * stdFun k g = stdFun k g * M}
  add_mem' := by
    intro M N hM hN g hg
    rw [Matrix.add_mul, Matrix.mul_add, hM g hg, hN g hg]
  zero_mem' := by
    intro g _
    rw [Matrix.zero_mul, Matrix.mul_zero]
  smul_mem' := by
    intro c M hM g hg
    rw [Matrix.smul_mul, Matrix.mul_smul, hM g hg]

theorem mem_commutant {H : Subgroup (Equiv.Perm (Fin 4))}
    {M : Matrix (Fin 3) (Fin 3) k} :
    M ∈ commutant k H ↔ ∀ g ∈ H, M * stdFun k g = stdFun k g * M := Iff.rfl

/-- The submodule form of `commutant_antitone`. -/
theorem commutant_antitone_subgroup {H H' : Subgroup (Equiv.Perm (Fin 4))}
    (hHH' : H ≤ H') : commutant k H' ≤ commutant k H :=
  fun _ hM g hg => hM g (hHH' hg)

/-- Scalars always commute. -/
theorem one_mem_commutant (H : Subgroup (Equiv.Perm (Fin 4))) :
    (1 : Matrix (Fin 3) (Fin 3) k) ∈ commutant k H := by
  intro g _
  rw [Matrix.one_mul, Matrix.mul_one]

/-- **The four-line computation.**  A matrix commuting with the images of the
two Klein involutions and of a three-cycle is a scalar.  The two diagonal
generators force `M` diagonal — this is the only step that uses
`(2 : k) ≠ 0` — and the three-cycle then forces the diagonal constant.

The `linear_combination` coefficients below are deliberately **not** uniform,
and the pattern is worth recording because nothing in the statement shows it.
Commuting with a diagonal `D` extracts, at entry `(i,j)`, the equation
`M i j * D j j = D i i * M i j`; whether that reads `-x = x` or `x = -x` depends
on which side of the diagonal the `-1` falls.  So `h01, h02, h12` take `-e`
while `h10, h20, h21` take `e`.  In `h22` the raw equation is
`-M 1 1 = -M 2 2`, which `simp` normalizes through `neg_inj` to `M 1 1 = M 2 2`,
and that reorientation is exactly why it needs `-e + h11` rather than `e + h11`.
The mathematical content is fixed and is the entrywise computation written out
in the module docstring. -/
theorem eq_smul_one_of_commutes (h2 : (2 : k) ≠ 0)
    {M : Matrix (Fin 3) (Fin 3) k}
    (c1 : M * d1 k = d1 k * M) (c2 : M * d2 k = d2 k * M)
    (c3 : M * d3 k = d3 k * M) :
    M = M 0 0 • (1 : Matrix (Fin 3) (Fin 3) k) := by
  have E1 : ∀ i j : Fin 3, (M * d1 k) i j = (d1 k * M) i j := fun i j => by rw [c1]
  have E2 : ∀ i j : Fin 3, (M * d2 k) i j = (d2 k * M) i j := fun i j => by rw [c2]
  have E3 : ∀ i j : Fin 3, (M * d3 k) i j = (d3 k * M) i j := fun i j => by rw [c3]
  have h01 : M 0 1 = 0 := by
    refine eq_zero_of_two_mul_eq_zero k h2 ?_
    have e := E1 0 1
    simp [d1, Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination -e
  have h02 : M 0 2 = 0 := by
    refine eq_zero_of_two_mul_eq_zero k h2 ?_
    have e := E1 0 2
    simp [d1, Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination -e
  have h10 : M 1 0 = 0 := by
    refine eq_zero_of_two_mul_eq_zero k h2 ?_
    have e := E1 1 0
    simp [d1, Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination e
  have h20 : M 2 0 = 0 := by
    refine eq_zero_of_two_mul_eq_zero k h2 ?_
    have e := E1 2 0
    simp [d1, Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination e
  have h12 : M 1 2 = 0 := by
    refine eq_zero_of_two_mul_eq_zero k h2 ?_
    have e := E2 1 2
    simp [d2, Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination -e
  have h21 : M 2 1 = 0 := by
    refine eq_zero_of_two_mul_eq_zero k h2 ?_
    have e := E2 2 1
    simp [d2, Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination e
  have h11 : M 1 1 = M 0 0 := by
    have e := E3 0 1
    simp [d3, Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h21] at e
    linear_combination -e
  have h22 : M 2 2 = M 0 0 := by
    have e := E3 1 2
    simp [d3, Matrix.mul_apply, Fin.sum_univ_three, h02, h10, h12] at e
    linear_combination -e + h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, h01, h02, h10, h20, h12, h21, h11, h22]

/-- **`End_{A₄}(V) = k·1`.**  The commutant of the alternating group in the
standard three-dimensional representation is exactly the scalars. -/
theorem commutant_alternatingGroup (h2 : (2 : k) ≠ 0) :
    commutant k (alternatingGroup (Fin 4)) = k ∙ (1 : Matrix (Fin 3) (Fin 3) k) := by
  refine le_antisymm ?_ ?_
  · intro M hM
    have hcomm := (mem_commutant k).mp hM
    have c1 : M * d1 k = d1 k * M := by
      rw [← stdFun_gen1 k h2]; exact hcomm gen1 gen1_mem
    have c2 : M * d2 k = d2 k * M := by
      rw [← stdFun_gen2 k h2]; exact hcomm gen2 gen2_mem
    have c3 : M * d3 k = d3 k * M := by
      rw [← stdFun_gen3 k h2]; exact hcomm gen3 gen3_mem
    rw [eq_smul_one_of_commutes k h2 c1 c2 c3]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact one_mem_commutant k _

/-- **The commutant does not separate `A₄ < S₄`.**  This is the manuscript's
sentence: the strictly larger subgroup has the *same* commutant, so the
candidate size cannot distinguish them. -/
theorem commutant_top_eq_commutant_alternatingGroup (h2 : (2 : k) ≠ 0) :
    commutant k ⊤ = commutant k (alternatingGroup (Fin 4)) := by
  refine le_antisymm (commutant_antitone_subgroup k le_top) ?_
  rw [commutant_alternatingGroup k h2, Submodule.span_le, Set.singleton_subset_iff]
  exact one_mem_commutant k _

/-- `End_{S₄}(V) = k·1` as well. -/
theorem commutant_top (h2 : (2 : k) ≠ 0) :
    commutant k ⊤ = k ∙ (1 : Matrix (Fin 3) (Fin 3) k) := by
  rw [commutant_top_eq_commutant_alternatingGroup k h2,
    commutant_alternatingGroup k h2]

/-- The candidate size assigns `1` to `A₄`. -/
theorem finrank_commutant_alternatingGroup (h2 : (2 : k) ≠ 0) :
    Module.finrank k (commutant k (alternatingGroup (Fin 4))) = 1 := by
  rw [commutant_alternatingGroup k h2]
  exact finrank_span_singleton one_ne_zero

/-- The candidate size assigns `1` to `S₄` too. -/
theorem finrank_commutant_top (h2 : (2 : k) ≠ 0) :
    Module.finrank k (commutant k (⊤ : Subgroup (Equiv.Perm (Fin 4)))) = 1 := by
  rw [commutant_top k h2]
  exact finrank_span_singleton one_ne_zero

/-- **`FD.20`, assembled.**  `A₄` is a proper subgroup of `S₄`, yet in the
standard three-dimensional representation the two commutants coincide and are
the scalars, so the candidate size `dim_k End_H(V)` takes the value `1` on
both.  Together with `commutant_antitone` — which says the size is
order-reversing — this is the whole content of the manuscript's remark. -/
theorem commutant_does_not_separate (h2 : (2 : k) ≠ 0) :
    alternatingGroup (Fin 4) < ⊤ ∧
      commutant k ⊤ = commutant k (alternatingGroup (Fin 4)) ∧
      commutant k (alternatingGroup (Fin 4)) = k ∙ (1 : Matrix (Fin 3) (Fin 3) k) ∧
      Module.finrank k (commutant k (alternatingGroup (Fin 4))) = 1 ∧
      Module.finrank k (commutant k (⊤ : Subgroup (Equiv.Perm (Fin 4)))) = 1 :=
  ⟨alternatingGroup_lt_top,
    commutant_top_eq_commutant_alternatingGroup k h2,
    commutant_alternatingGroup k h2,
    finrank_commutant_alternatingGroup k h2,
    finrank_commutant_top k h2⟩

end StandardRepCommutant

/-- **`FD.20` over `ℂ`**: `A₄ < S₄` strictly, and the commutants of the two in
the standard three-dimensional representation are both `ℂ · 1`, of dimension
`1`. -/
theorem standardRep_commutant_does_not_separate_complex :
    alternatingGroup (Fin 4) < ⊤ ∧
      StandardRepCommutant.commutant ℂ ⊤
        = StandardRepCommutant.commutant ℂ (alternatingGroup (Fin 4)) ∧
      StandardRepCommutant.commutant ℂ (alternatingGroup (Fin 4))
        = ℂ ∙ (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
      Module.finrank ℂ
          (StandardRepCommutant.commutant ℂ (alternatingGroup (Fin 4))) = 1 ∧
      Module.finrank ℂ
          (StandardRepCommutant.commutant ℂ (⊤ : Subgroup (Equiv.Perm (Fin 4)))) = 1 :=
  StandardRepCommutant.commutant_does_not_separate ℂ (by norm_num)

end GroupApproximation
