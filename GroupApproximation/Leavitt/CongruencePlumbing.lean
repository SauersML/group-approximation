import GroupApproximation.Leavitt.CongruenceSubgroups
import GroupApproximation.Leavitt.ElementarySimplicity

/-!
# Entrywise plumbing for the congruence subgroups `C_ι(R, I)`

`GroupApproximation.Leavitt.CongruenceSubgroups` defines `congruenceSubgroup ι I`
-- the manuscript's `C_n(R, I)` -- by a *scalar* condition: a unit of `M_ι(R)`
lies in it when it is congruent modulo `I`, entrywise, to a constant diagonal
matrix whose coefficient is central modulo `I`.  The literature states the same
subgroup by an *entrywise* condition (Preusser, *On general linear groups over
exchange rings*, Linear and Multilinear Algebra **70** (2022), Remark 11):

* every off-diagonal entry of `u` lies in `I`, and
* `a * u i i - u j j * a ∈ I` for all `i j : ι` and all `a : R`.

This file proves that the two descriptions agree
(`mem_congruenceSubgroup_iff_entries`), records monotonicity of the congruence
subgroup in its level (`congruenceSubgroup_mono`), and repackages the entrywise
description in the shape a subgroup of `EL_ι(R)` presents it in
(`map_le_congruenceSubgroup_of_entries`).

## What is *not* here

Nothing below proves an upper-sandwich inclusion.  The entrywise clauses
`hoff` and `hdiag` of `map_le_congruenceSubgroup_of_entries` are hypotheses;
supplying them for the level ideal of a normal subgroup is precisely the
content of the cited normal-structure theorem, which remains unformalized.
This file only converts one description of the target subgroup into the other.

## Hypotheses

All three statements hold over an arbitrary unital ring, for an arbitrary
finite index type, with **no** cardinality bound on `ι`.  In particular:

* `mem_congruenceSubgroup_iff_entries` takes a single index `i₀ : ι`, used only
  to name the scalar `lam := u i₀ i₀`; it does not need `1 < Fintype.card ι`.
  Both directions of the equivalence are proved from the two entrywise clauses
  alone, the relative-centre clause being the case `i = j = i₀` of the diagonal
  clause.
* `map_le_congruenceSubgroup_of_entries` needs no index at all: when `ι` is
  empty the defining condition is vacuous and the scalar `0` serves.  It also
  does not need `N` to be normal.
-/

namespace GroupApproximation

open ElementarySimplicity

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-! ### Monotonicity in the level -/

/-- **The congruence subgroup grows with its level.**  Both clauses of the
defining condition -- centrality of the scalar modulo the level, and
membership of the entries of `u - lam • 1` in the level -- are membership
statements in the ideal, so they are inherited along `I ≤ J` with the same
scalar. -/
theorem congruenceSubgroup_mono {I J : TwoSidedIdeal R} (hIJ : I ≤ J) :
    congruenceSubgroup ι I ≤ congruenceSubgroup ι J := by
  rintro u ⟨lam, hlam, hu⟩
  refine mem_congruenceSubgroup.mpr ⟨lam, mem_relativeCenter.mpr ?_, ?_⟩
  · exact fun x ↦ hIJ (mem_relativeCenter.mp hlam x)
  · exact fun i j ↦ hIJ (hu i j)

/-! ### The entrywise description -/

/-- **The entrywise description of `C_ι(R, I)`** (Preusser's Remark 11).  A
unit of `M_ι(R)` is congruent modulo `I` to a constant diagonal matrix with
coefficient central modulo `I` exactly when its off-diagonal entries lie in `I`
and its diagonal entries all commute with `R` modulo `I` in the two-index sense
`a * u i i - u j j * a ∈ I`.

The index `i₀` is used only to name the scalar in the reverse direction; no
cardinality assumption on `ι` is needed. -/
theorem mem_congruenceSubgroup_iff_entries (i₀ : ι) {I : TwoSidedIdeal R}
    {u : (Matrix ι ι R)ˣ} :
    u ∈ congruenceSubgroup ι I ↔
      (∀ i j : ι, i ≠ j → (u : Matrix ι ι R) i j ∈ I) ∧
      (∀ (i j : ι) (a : R),
        a * (u : Matrix ι ι R) i i - (u : Matrix ι ι R) j j * a ∈ I) := by
  constructor
  · rintro ⟨lam, hlam, hu⟩
    refine ⟨fun i j hij ↦ ?_, fun i j a ↦ ?_⟩
    · have h := hu i j
      rwa [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, sub_zero] at h
    · have hi := hu i i
      have hj := hu j j
      rw [Matrix.sub_apply, Matrix.diagonal_apply_eq] at hi hj
      have key : a * (u : Matrix ι ι R) i i - (u : Matrix ι ι R) j j * a
          = a * ((u : Matrix ι ι R) i i - lam) - (lam * a - a * lam)
            - ((u : Matrix ι ι R) j j - lam) * a := by
        noncomm_ring
      rw [key]
      exact I.sub_mem
        (I.sub_mem (I.mul_mem_left _ _ hi) (mem_relativeCenter.mp hlam a))
        (I.mul_mem_right _ _ hj)
  · rintro ⟨hoff, hdiag⟩
    refine mem_congruenceSubgroup.mpr
      ⟨(u : Matrix ι ι R) i₀ i₀, mem_relativeCenter.mpr ?_, fun i j ↦ ?_⟩
    · intro x
      have h := hdiag i₀ i₀ x
      have key : (u : Matrix ι ι R) i₀ i₀ * x - x * (u : Matrix ι ι R) i₀ i₀
          = -(x * (u : Matrix ι ι R) i₀ i₀ - (u : Matrix ι ι R) i₀ i₀ * x) :=
        (neg_sub _ _).symm
      rw [key]
      exact I.neg_mem h
    · by_cases hij : i = j
      · rw [Matrix.sub_apply, hij, Matrix.diagonal_apply_eq]
        have h := hdiag j i₀ 1
        rwa [one_mul, mul_one] at h
      · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, sub_zero]
        exact hoff i j hij

/-! ### The shape a subgroup of `EL_ι(R)` presents -/

/-- **Entrywise membership implies the upper sandwich.**  If every element of
`N ≤ EL_ι(R)` has off-diagonal entries in `I` and diagonal entries satisfying
the two-index commutation `a * g i i - g j j * a ∈ I`, then the image of `N` in
`GL_ι(R)` lies in the full congruence subgroup of level `I`.

Both hypotheses are inputs: this lemma is the translation step only, and does
not establish them.  It needs neither a cardinality bound on `ι` nor normality
of `N`. -/
theorem map_le_congruenceSubgroup_of_entries
    (N : Subgroup (elementaryGroup ι R)) (I : TwoSidedIdeal R)
    (hoff : ∀ g ∈ N, ∀ i j : ι, i ≠ j → elMat g i j ∈ I)
    (hdiag : ∀ g ∈ N, ∀ (i j : ι) (a : R),
      a * elMat g i i - elMat g j j * a ∈ I) :
    N.map (elementaryGroup ι R).subtype ≤ congruenceSubgroup ι I := by
  rintro u ⟨g, hg, rfl⟩
  rcases isEmpty_or_nonempty ι with hempty | hne
  · exact mem_congruenceSubgroup.mpr
      ⟨0, zero_mem_relativeCenter I, fun i ↦ (hempty.false i).elim⟩
  · obtain ⟨i₀⟩ := hne
    exact (mem_congruenceSubgroup_iff_entries i₀).mpr
      ⟨fun i j hij ↦ hoff g hg i j hij, fun i j a ↦ hdiag g hg i j a⟩

end GroupApproximation
