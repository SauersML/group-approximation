import GroupApproximation.Leavitt.RowAnnihilatorTransvection

/-!
# Being normalized by `EL_ι(R)`: the commutator plumbing

Preusser's Theorem 3 (*On general linear groups over exchange rings*, Linear
and Multilinear Algebra **70** (2022), no. 4, 705--713) classifies every
subgroup `H ≤ GL_ι(R)` that is **normalized by** `EL_ι(R)`, not merely the
normal subgroups of `EL_ι(R)`.  The repository's existing chain
(`Leavitt.RowAnnihilatorTransvection`, `Leavitt.PreusserSandwichStep`,
`Leavitt.PreusserAssembly`) is typed over `Subgroup (elementaryGroup ι R)` with
a `[N.Normal]` instance.  This file supplies the two pieces of scaffolding that
let the same computations be rerun one level up, inside `GL_ι(R)`.

## `NormalizedBy`

`NormalizedBy H E` says that every `E`-conjugate of an element of `H` is again
in `H`.  It is exactly `E ≤ H.normalizer` (`NormalizedBy.of_le_normalizer`,
`NormalizedBy.le_normalizer`), stated in the elimination form the commutator
computations consume.

The point is that all of Preusser's manipulations are commutators of an element
of `H` with *elementary* elements, and those never leave `H`:

* `NormalizedBy.commutator_mem_left`  : `x ∈ H`, `y ∈ E` ⟹ `⁅x, y⁆ ∈ H`;
* `NormalizedBy.commutator_mem_right` : `y ∈ E`, `x ∈ H` ⟹ `⁅y, x⁆ ∈ H`;
* `NormalizedBy.arrow_step_mem` : the membership form of Preusser's Lemma 19,
  with the two conjugating elements required to lie in `E`.  Only `a` and `g`
  are conjugated in the identity
  `⁅a⁻¹, g⁆ * ⁅g, b⁆ = a⁻¹ (g (ab) g⁻¹) a · (a⁻¹ (ab) a)⁻¹`, and in every
  application both are elementary, while `b` -- which is where the general
  linear element hides -- is never conjugated.

Normality of `H` in `E` is *not* assumed, and `H` is not assumed to be
contained in `E`.

## `glMat`

`ElementarySimplicity.elMat` is the underlying matrix of an element of
`EL_ι(R)`.  `glMat` is the same coercion for an element of `GL_ι(R)`, with the
same rewriting interface (`glMat_mul`, `glMat_mul_inv`, `glMat_inv_mul`,
`glMat_elementaryUnit`, `glMat_elementaryUnit_inv`, `glMat_injective`).  Every
lemma is `rfl` or a one-line `Units` fact; the purpose is purely that the
ported computations then read exactly like the originals.

The column matrix `RowAnnihilator.colUnitMat j x` -- the elementary matrix
whose `j`-th column is `x` -- is reused verbatim from the normal-subgroup
chain; only its entry formulas are restated through `glMat`.
-/

namespace GroupApproximation
namespace PreusserNormalizedBy

open scoped commutatorElement

/-! ### Subgroups normalized by a subgroup -/

section Group

variable {G : Type*} [Group G]

/-- `H` is **normalized by** `E`: every `E`-conjugate of an element of `H` is
again in `H`. -/
def NormalizedBy (H E : Subgroup G) : Prop :=
  ∀ e ∈ E, ∀ h ∈ H, e * h * e⁻¹ ∈ H

namespace NormalizedBy

variable {H E : Subgroup G}

theorem conj_mem (hnorm : NormalizedBy H E) {e : G} (he : e ∈ E) {h : G}
    (hh : h ∈ H) : e * h * e⁻¹ ∈ H :=
  hnorm e he h hh

theorem conj_mem' (hnorm : NormalizedBy H E) {e : G} (he : e ∈ E) {h : G}
    (hh : h ∈ H) : e⁻¹ * h * e ∈ H := by
  have h1 := hnorm e⁻¹ (E.inv_mem he) h hh
  rwa [inv_inv] at h1

/-- `NormalizedBy` is the elimination form of `E ≤ H.normalizer`. -/
theorem of_le_normalizer (h : E ≤ Subgroup.normalizer (H : Set G)) :
    NormalizedBy H E :=
  fun _e he x hx ↦ (Subgroup.mem_normalizer_iff.mp (h he) x).mp hx

/-- ... and conversely. -/
theorem le_normalizer (hnorm : NormalizedBy H E) :
    E ≤ Subgroup.normalizer (H : Set G) := by
  intro e he
  refine Subgroup.mem_normalizer_iff.mpr fun x ↦ ⟨fun hx ↦ hnorm e he x hx, ?_⟩
  intro hx
  have h2 := hnorm e⁻¹ (E.inv_mem he) _ hx
  have hid : e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x := by group
  rwa [hid] at h2

/-- A commutator with its **left** entry in `H` and its right entry in `E` lies
in `H`: `⁅x, y⁆ = x * (y x⁻¹ y⁻¹)`. -/
theorem commutator_mem_left (hnorm : NormalizedBy H E) {x : G} (hx : x ∈ H)
    {y : G} (hy : y ∈ E) : ⁅x, y⁆ ∈ H := by
  have hid : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
    rw [commutatorElement_def, mul_assoc x y x⁻¹, mul_assoc x (y * x⁻¹) y⁻¹]
  rw [hid]
  exact H.mul_mem hx (hnorm.conj_mem hy (H.inv_mem hx))

/-- A commutator with its **right** entry in `H` and its left entry in `E` lies
in `H`. -/
theorem commutator_mem_right (hnorm : NormalizedBy H E) {y : G} (hy : y ∈ E)
    {x : G} (hx : x ∈ H) : ⁅y, x⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (hnorm.conj_mem hy hx) (H.inv_mem hx)

/-- **The arrow step**, for a subgroup merely normalized by `E`.

This is `RowAnnihilator.arrow_step_mem` with the normality of the target
subgroup replaced by the hypothesis that the two elements actually conjugated
-- `a` and `g` -- lie in `E`.  The element `b`, which in every application
carries the general linear factor, is never conjugated. -/
theorem arrow_step_mem (hnorm : NormalizedBy H E) {a b : G} (hab : a * b ∈ H)
    (ha : a ∈ E) {g : G} (hg : g ∈ E) : ⁅a⁻¹, g⁆ * ⁅g, b⁆ ∈ H := by
  have hkey : ⁅a⁻¹, g⁆ * ⁅g, b⁆
      = a⁻¹ * (g * (a * b) * g⁻¹) * a * (a⁻¹ * (a * b) * a)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hkey]
  exact H.mul_mem (hnorm.conj_mem' ha (hnorm.conj_mem hg hab))
    (H.inv_mem (hnorm.conj_mem' ha hab))

end NormalizedBy

end Group

/-! ### The matrix of an element of `GL_ι(R)` -/

section Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The underlying matrix of an element of `GL_ι(R)`.  This is to
`(Matrix ι ι R)ˣ` what `ElementarySimplicity.elMat` is to `elementaryGroup`. -/
def glMat (u : (Matrix ι ι R)ˣ) : Matrix ι ι R := (u : Matrix ι ι R)

@[simp] theorem glMat_mul (u v : (Matrix ι ι R)ˣ) :
    glMat (u * v) = glMat u * glMat v := rfl

theorem glMat_mul_inv (u : (Matrix ι ι R)ˣ) : glMat u * glMat u⁻¹ = 1 :=
  u.mul_inv

theorem glMat_inv_mul (u : (Matrix ι ι R)ˣ) : glMat u⁻¹ * glMat u = 1 :=
  u.inv_mul

@[simp] theorem glMat_elementaryUnit (i j : ι) (hij : i ≠ j) (a : R) :
    glMat (elementaryUnit i j hij a) = 1 + Matrix.single i j a := rfl

@[simp] theorem glMat_elementaryUnit_inv (i j : ι) (hij : i ≠ j) (a : R) :
    glMat ((elementaryUnit i j hij a)⁻¹) = 1 - Matrix.single i j a := rfl

/-- The inverse of an elementary unit negates its coefficient. -/
theorem elementaryUnit_inv (i j : ι) (h : i ≠ j) (a : R) :
    (elementaryUnit i j h a)⁻¹ = elementaryUnit i j h (-a) :=
  inv_eq_of_mul_eq_one_right
    (by rw [elementaryUnit_mul, add_neg_cancel, elementaryUnit_zero])

theorem glMat_sqZeroUnit (A : Matrix ι ι R) (hA : A * A = 0) :
    glMat (sqZeroUnit A hA) = 1 + A := rfl

theorem glMat_injective :
    Function.Injective (glMat : (Matrix ι ι R)ˣ → Matrix ι ι R) :=
  fun _ _ h ↦ Units.ext h

/-- The matrix of an element of `EL_ι(R)`, read in `GL_ι(R)`, is its `elMat`. -/
theorem glMat_coe (g : elementaryGroup ι R) :
    glMat ((elementaryGroup ι R).subtype g) = ElementarySimplicity.elMat g := rfl

/-! #### The column matrix, through `glMat` -/

theorem glMat_colUnitMat (j : ι) (x : ι → R) :
    glMat (RowAnnihilator.colUnitMat j x) = 1 + RowAnnihilator.colDefect j x :=
  rfl

theorem glMat_colUnitMat_inv (j : ι) (x : ι → R) :
    glMat ((RowAnnihilator.colUnitMat j x)⁻¹)
      = 1 - RowAnnihilator.colDefect j x := rfl

/-- The prescribed column, in the presence of the normalisation `x j = 1`. -/
theorem glMat_colUnitMat_apply_col {j : ι} {x : ι → R} (hxj : x j = 1) (p : ι) :
    glMat (RowAnnihilator.colUnitMat j x) p j = x p := by
  rw [glMat_colUnitMat, Matrix.add_apply, RowAnnihilator.colDefect_apply,
    if_pos rfl]
  by_cases hp : p = j
  · rw [if_pos hp, hp, Matrix.one_apply_eq, add_zero, hxj]
  · rw [if_neg hp, Matrix.one_apply_ne hp, zero_add]

/-- Away from column `j` the column matrix is the identity. -/
theorem glMat_colUnitMat_apply_of_ne (j : ι) (x : ι → R) (p : ι) {q : ι}
    (hq : q ≠ j) :
    glMat (RowAnnihilator.colUnitMat j x) p q = if p = q then 1 else 0 := by
  rw [glMat_colUnitMat, Matrix.add_apply,
    RowAnnihilator.colDefect_apply_of_ne j x p hq, add_zero, Matrix.one_apply]

theorem colUnitMat_mem_elementaryGroup (j : ι) (x : ι → R) :
    RowAnnihilator.colUnitMat j x ∈ elementaryGroup ι R :=
  RowAnnihilator.colUnitMat_mem j x

end Matrix

end PreusserNormalizedBy
end GroupApproximation
