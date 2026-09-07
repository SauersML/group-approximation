import GroupApproximation.KOne.ClassicalKOne
import GroupApproximation.Leavitt.Whitehead
import GroupApproximation.Meta.AxiomGuard

/-!
# Whitehead's lemma for the stable general linear group of a ring

`non_mf_groups_exist.tex`, the paragraph preceding Theorem
`thm:mf-quotient-units`:

> Let `GL(R)` and `EL(R)` be the direct limits of `GL_n(R)` and `EL_n(R)` along
> `A ↦ diag(A, 1)`; the subgroup `EL(R)` is normal in `GL(R)` by Whitehead's
> lemma, and `K_1(R) = GL(R)/EL(R)`.

This module proves that printed sentence's first clause, over an arbitrary
unital ring and with nothing assumed: `E_∞(R)` contains the commutator subgroup
of `GL(R)`, hence is normal, with abelian quotient.

## What is reused and what is new

The Whitehead factorization itself is **not** proved here.  `Leavitt/Whitehead.lean`
already carries it over an arbitrary ring, in matrix form:

* `Whitehead.whitehead_diagonal : diag(a, a⁻¹) = w a * w (-1)`, a product of six
  transvections, and `whitehead_diagonal_mem`;
* `Whitehead.whitehead_commutator_mem (a b : Aˣ) : diag(⁅a,b⁆, 1) ∈ elementary2 A`.

What was missing is that those results are stated for the submonoid
`Whitehead.elementary2 A` of `M₂(A)` — matrices, not units — and that nothing
connected them to `elementaryGroup`, the subgroup of `GL₂(A)` from which
`KOne/ClassicalKOne.lean` builds the colimit `E_∞(R)`.  Before this module
nothing outside `Leavitt/Whitehead.lean` itself referred to `elementary2` at
all.  Two steps supply the connection:

* `exists_unit_of_mem_elementary2`: every matrix of `elementary2 S` is the value
  of a unit of `elementaryGroup (Fin 2) S`.  Both generating families are values
  of elementary units, so this is a submonoid-closure induction, not a new
  computation.
* `twoBlockUnitEquiv`: the flattening `GL₂(Mₙ(R)) ≅ GL_{n+n}(R)`, assembled from
  `elementaryBlockUnitEquiv` and `elementaryReindexUnitEquiv` of
  `Leavitt/ElementaryGroup.lean`, which already carry elementary subgroups onto
  elementary subgroups.  The one genuinely new computation is
  `twoBlockUnitEquiv_val_of_diagonalPair`: under that flattening the `2 × 2`
  block matrix `diag(X, 1)` becomes exactly `stabMatrix (n+n) X`, the padding the
  direct system of `ClassicalKOne` transitions along.  Reconciling those two
  descriptions of the same block picture — one by `Matrix.comp` at index pairs,
  one by `padEntry` at natural numbers — is what the four-case analysis does.

## Rank, and why `n + n`

The factorization needs `X` and `X⁻¹` on the diagonal together, so it lives at
rank `2n`; `n + n` rather than `2 * n` is what makes `Fin.castAdd`/`Fin.natAdd`
and `padEntry`'s `< n` test line up with no multiplication lemma in between.
Nothing downstream sees the choice, since the colimit identifies every rank.

## No hypothesis

Everything below holds over an arbitrary unital ring, with no countability, no
finiteness, and no literature input.
-/

namespace GroupApproximation
namespace StableWhitehead

open scoped commutatorElement

/-! ### Three facts about `Fin 2` -/

theorem fin2_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

theorem fin2_one_ne_zero : (1 : Fin 2) ≠ 0 := by decide

/-- The case split on `Fin 2`, as a disjunction.

Stated rather than left to `fin_cases`, which introduces the anonymous
constructor form `⟨0, _⟩` in place of the literal `0` and so blocks rewriting by
lemmas keyed on the literal. -/
theorem fin2_eq_zero_or_one (b : Fin 2) : b = 0 ∨ b = 1 := by
  obtain ⟨v, hv⟩ := b
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ### From the elementary submonoid of `M₂(S)` to the elementary subgroup of
`GL₂(S)` -/

section Bridge

variable {S : Type*} [Ring S]

/-- The upper transvection of `Leavitt/Whitehead.lean` is the value of the
elementary unit `x₀₁(a)`. -/
theorem elementaryUnit_val_x12 (a : S) :
    ((elementaryUnit (0 : Fin 2) 1 fin2_zero_ne_one a :
        (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S)
      = Whitehead.x12 a := by
  show (1 : Matrix (Fin 2) (Fin 2) S) + Matrix.single (0 : Fin 2) 1 a
    = Whitehead.x12 a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Whitehead.x12]

/-- The lower transvection of `Leavitt/Whitehead.lean` is the value of the
elementary unit `x₁₀(a)`. -/
theorem elementaryUnit_val_x21 (a : S) :
    ((elementaryUnit (1 : Fin 2) 0 fin2_one_ne_zero a :
        (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S)
      = Whitehead.x21 a := by
  show (1 : Matrix (Fin 2) (Fin 2) S) + Matrix.single (1 : Fin 2) 0 a
    = Whitehead.x21 a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Whitehead.x21]

/-- **Every matrix of the rank-two elementary submonoid is an elementary
unit.**  `Whitehead.elementary2 S` is a submonoid of `M₂(S)`; its two generating
families are values of elementary units, so the whole submonoid lies in the
image of `elementaryGroup (Fin 2) S`. -/
theorem exists_unit_of_mem_elementary2 {M : Matrix (Fin 2) (Fin 2) S}
    (hM : M ∈ Whitehead.elementary2 S) :
    ∃ z : (Matrix (Fin 2) (Fin 2) S)ˣ,
      z ∈ elementaryGroup (Fin 2) S ∧ (z : Matrix (Fin 2) (Fin 2) S) = M := by
  have hle : Whitehead.elementary2 S ≤
      Submonoid.map (Units.coeHom (Matrix (Fin 2) (Fin 2) S))
        (elementaryGroup (Fin 2) S).toSubmonoid := by
    rw [Whitehead.elementary2, Submonoid.closure_le]
    rintro N ⟨a, ha | ha⟩
    · refine ⟨elementaryUnit (0 : Fin 2) 1 fin2_zero_ne_one a,
        elementaryUnit_mem _ _ _ a, ?_⟩
      show ((elementaryUnit (0 : Fin 2) 1 fin2_zero_ne_one a :
        (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S) = N
      rw [ha]
      exact elementaryUnit_val_x12 a
    · refine ⟨elementaryUnit (1 : Fin 2) 0 fin2_one_ne_zero a,
        elementaryUnit_mem _ _ _ a, ?_⟩
      show ((elementaryUnit (1 : Fin 2) 0 fin2_one_ne_zero a :
        (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S) = N
      rw [ha]
      exact elementaryUnit_val_x21 a
  obtain ⟨z, hz, hzval⟩ := hle hM
  exact ⟨z, hz, hzval⟩

end Bridge

/-! ### The two-block flattening `GL₂(Mₙ(R)) ≅ GL_{n+n}(R)` -/

section TwoBlock

variable {R : Type*} [Ring R]

/-- The two-block splitting `Fin 2 × Fin n ≃ Fin (n + n)`: `(0, k) ↦ k` and
`(1, k) ↦ n + k`.

Composed from Mathlib's equivalences rather than written out, so that it carries
no proof obligation of its own; the two facts the entry computation needs are
`val_blockIdx_zero` and `val_blockIdx_one` below. -/
def blockIdx (n : ℕ) : Fin 2 × Fin n ≃ Fin (n + n) :=
  ((finTwoEquiv.prodCongr (Equiv.refl (Fin n))).trans
    (Equiv.boolProdEquivSum (Fin n))).trans finSumFinEquiv

theorem val_blockIdx_zero (n : ℕ) (k : Fin n) :
    ((blockIdx n ((0 : Fin 2), k) : Fin (n + n)) : ℕ) = (k : ℕ) := by
  simp [blockIdx, finTwoEquiv]

theorem val_blockIdx_one (n : ℕ) (k : Fin n) :
    ((blockIdx n ((1 : Fin 2), k) : Fin (n + n)) : ℕ) = n + (k : ℕ) := by
  simp [blockIdx, finTwoEquiv]
  omega

/-- The flattening `GL₂(Mₙ(R)) ≅ GL_{n+n}(R)`: block composition followed by the
two-block reindexing. -/
def twoBlockUnitEquiv (R : Type*) [Ring R] (n : ℕ) :
    (Matrix (Fin 2) (Fin 2) (Matrix (Fin n) (Fin n) R))ˣ ≃*
      (Matrix (Fin (n + n)) (Fin (n + n)) R)ˣ :=
  (elementaryBlockUnitEquiv (ι := Fin 2) (κ := Fin n) (R := R)).trans
    (elementaryReindexUnitEquiv (R := R) (blockIdx n))

theorem twoBlockUnitEquiv_val (n : ℕ)
    (z : (Matrix (Fin 2) (Fin 2) (Matrix (Fin n) (Fin n) R))ˣ) :
    ((twoBlockUnitEquiv R n z : (Matrix (Fin (n + n)) (Fin (n + n)) R)ˣ) :
        Matrix (Fin (n + n)) (Fin (n + n)) R)
      = Matrix.reindex (blockIdx n) (blockIdx n)
          (Matrix.comp (Fin 2) (Fin 2) (Fin n) (Fin n) R
            (z : Matrix (Fin 2) (Fin 2) (Matrix (Fin n) (Fin n) R))) := rfl

/-- **The flattening carries the elementary subgroup into the elementary
subgroup.**  Both halves are proved in `Leavitt/ElementaryGroup.lean`:
`elementaryBlockGroup_map` for the block composition, `elementaryReindexGroup_map`
for the reindexing. -/
theorem twoBlockUnitEquiv_elementary {n : ℕ}
    {z : (Matrix (Fin 2) (Fin 2) (Matrix (Fin n) (Fin n) R))ˣ}
    (hz : z ∈ elementaryGroup (Fin 2) (Matrix (Fin n) (Fin n) R)) :
    twoBlockUnitEquiv R n z ∈ elementaryGroup (Fin (n + n)) R := by
  have h1 : elementaryBlockUnitEquiv (ι := Fin 2) (κ := Fin n) (R := R) z ∈
      elementaryGroup (Fin 2 × Fin n) R := by
    rw [← elementaryBlockGroup_map (ι := Fin 2) (κ := Fin n) (R := R)]
    exact Subgroup.mem_map_of_mem _ hz
  have h2 := Subgroup.mem_map_of_mem
    (elementaryReindexUnitEquiv (R := R) (blockIdx n)).toMonoidHom h1
  rwa [elementaryReindexGroup_map] at h2

/-- **The flattening of `diag(X, 1)` is the padding.**  This is the module's one
new computation: the `2 × 2` block description of `diag(X, 1)`, read through
`Matrix.comp` at index pairs, agrees entry for entry with `stabMatrix (n+n) X`,
read through `padEntry` at natural numbers. -/
theorem twoBlockUnitEquiv_val_of_diagonalPair {n : ℕ}
    (X : (Matrix (Fin n) (Fin n) R)ˣ)
    (z : (Matrix (Fin 2) (Fin 2) (Matrix (Fin n) (Fin n) R))ˣ)
    (hz : (z : Matrix (Fin 2) (Fin 2) (Matrix (Fin n) (Fin n) R))
      = Whitehead.diagonalPair (X : Matrix (Fin n) (Fin n) R) 1) :
    twoBlockUnitEquiv R n z
      = glStab R n (n + n) (Nat.le_add_right n n) X := by
  apply Units.ext
  rw [twoBlockUnitEquiv_val, glStab_val, hz]
  ext x y
  obtain ⟨⟨b, k⟩, rfl⟩ := (blockIdx n).surjective x
  obtain ⟨⟨c, l⟩, rfl⟩ := (blockIdx n).surjective y
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.comp_apply, stabMatrix_apply]
  rcases fin2_eq_zero_or_one b with rfl | rfl <;>
    rcases fin2_eq_zero_or_one c with rfl | rfl
  · -- both indices inside the corner
    rw [val_blockIdx_zero, val_blockIdx_zero,
      padEntry_of_lt_lt _ k.isLt l.isLt]
    simp [Whitehead.diagonalPair]
  · -- row inside the corner, column outside
    have hy : ¬ ((n + (l : ℕ)) < n) := by omega
    rw [val_blockIdx_zero, val_blockIdx_one, padEntry_of_lt_ge _ k.isLt hy]
    simp [Whitehead.diagonalPair]
  · -- row outside the corner, column inside
    have hx : ¬ ((n + (k : ℕ)) < n) := by omega
    have hne : ¬ ((n + (k : ℕ)) = (l : ℕ)) := by
      have := l.isLt
      omega
    rw [val_blockIdx_one, val_blockIdx_zero, padEntry_of_ge _ hx, if_neg hne]
    simp [Whitehead.diagonalPair]
  · -- both indices outside the corner
    have hx : ¬ ((n + (k : ℕ)) < n) := by omega
    rw [val_blockIdx_one, val_blockIdx_one, padEntry_of_ge _ hx]
    by_cases hkl : k = l
    · subst hkl
      simp [Whitehead.diagonalPair]
    · have hne : ¬ ((n + (k : ℕ)) = n + (l : ℕ)) := fun hc =>
        hkl (Fin.ext (by omega))
      rw [if_neg hne]
      simp [Whitehead.diagonalPair, hkl]

end TwoBlock

/-! ### Whitehead's lemma in the colimit -/

section Colimit

variable (R : Type*) [Ring R]

/-- **The padded commutator is elementary at rank `n + n`.**  This is
`Whitehead.whitehead_commutator_mem`, carried across the two bridges above. -/
theorem glStab_commutator_mem {n : ℕ} (u v : (Matrix (Fin n) (Fin n) R)ˣ) :
    glStab R n (n + n) (Nat.le_add_right n n) ⁅u, v⁆
      ∈ elementaryGroup (Fin (n + n)) R := by
  have hmem : Whitehead.diagonalPair
      ((⁅u, v⁆ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) 1
        ∈ Whitehead.elementary2 (Matrix (Fin n) (Fin n) R) := by
    rw [commutatorElement_def u v]
    exact Whitehead.whitehead_commutator_mem u v
  obtain ⟨z, hz, hzval⟩ := exists_unit_of_mem_elementary2 hmem
  have hz' := twoBlockUnitEquiv_elementary (R := R) hz
  rwa [twoBlockUnitEquiv_val_of_diagonalPair ⁅u, v⁆ z hzval] at hz'

/-- **Whitehead's lemma.**  The elementary subgroup of the stable general linear
group contains its commutator subgroup.

Two elements of the colimit are represented at a common rank `n`; their
commutator, padded to rank `n + n`, is elementary by `glStab_commutator_mem`,
and padding does not change the class. -/
theorem commutator_le_elementaryColim :
    commutator (ClassicalGLColim R) ≤ elementaryColim R := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨n, u, v, rfl, rfl⟩ :=
    DirectLimit.exists_eq_mk₂ (f := glStab R) x y
  have hx : (⟦⟨n, u⟩⟧ : ClassicalGLColim R) = glColimOf R n u := rfl
  have hy : (⟦⟨n, v⟩⟧ : ClassicalGLColim R) = glColimOf R n v := rfl
  rw [hx, hy, ← map_commutatorElement,
    ← glColimOf_glStab (R := R) (Nat.le_add_right n n) ⁅u, v⁆]
  exact glColimOf_mem_elementaryColim R (glStab_commutator_mem R u v)

/-- **The printed sentence**: `EL(R)` is normal in `GL(R)`, by Whitehead's
lemma.  A subgroup containing the commutator subgroup is normal, because
`g h g⁻¹ = ⁅g, h⁆ * h`. -/
instance elementaryColim_normal : (elementaryColim R).Normal := by
  constructor
  intro h hh g
  have hc : ⁅g, h⁆ ∈ elementaryColim R :=
    commutator_le_elementaryColim R (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top g) (Subgroup.mem_top h))
  have hsplit : g * h * g⁻¹ = ⁅g, h⁆ * h := by
    rw [commutatorElement_def]
    group
  rw [hsplit]
  exact (elementaryColim R).mul_mem hc hh

end Colimit

end StableWhitehead
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.StableWhitehead.exists_unit_of_mem_elementary2
#audit_axioms GroupApproximation.StableWhitehead.twoBlockUnitEquiv_val_of_diagonalPair
#audit_axioms GroupApproximation.StableWhitehead.glStab_commutator_mem
#audit_axioms GroupApproximation.StableWhitehead.commutator_le_elementaryColim
#audit_axioms GroupApproximation.StableWhitehead.elementaryColim_normal
