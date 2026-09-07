import GroupApproximation.Leavitt.AryLeavitt
import GroupApproximation.Leavitt.Leavitt
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# `cor:simple-infinite-ring`: where the printed fullness hypothesis comes from

`non_mf_groups_exist.tex`, Corollary `cor:simple-infinite-ring` and its proof:

> In the first case choose `ts = 1 ≠ st`; then `1 - st` is a nonzero
> idempotent, and since `R` is simple it generates `R` as a two-sided ideal.
> In the second case, with generators `s₁,…,s_m,t₁,…,t_m` subject to
> `tᵢsⱼ = δᵢⱼ` and `∑ᵢ sᵢtᵢ = 1`, take `s = s₁` and `t = t₁`; then
> `1 - s₁t₁ = ∑_{i≥2} sᵢtᵢ` and `t₂(1 - s₁t₁)s₂ = 1`.

This module supplies exactly the two fullness verifications, in the explicit
form the manuscript itself glosses the ideal condition with:

> `R(1-st) R = R` … the hypothesis says that `∑_j a_j(1-st)b_j = 1` for
> finitely many `a_j, b_j ∈ R`.

No property `(T)`, no group and no MF predicate occurs here; the module is
pure ring theory, and its two theorems are what `thm:full-defect-ring` is
applied to in the corollary.

## The simple case, and why the ideal is built by hand

The printed step "since `R` is simple it generates `R` as a two-sided ideal"
needs the *finite-sum* form of the generated ideal, because that is the form
the group-theoretic argument consumes (each summand `a_j e b_j` contributes one
elementary matrix to a product).  Mathlib's `TwoSidedIdeal.span {e}` is
characterised through an additive closure
(`TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure`), not through an indexed
sum, so the set of finite sums `∑_k a_k e b_k` is assembled directly as a
two-sided ideal with `TwoSidedIdeal.mk'`.  It contains `e = 1·e·1`, so if
`e ≠ 0` then simplicity forces it to contain `1`, which is the printed
conclusion in the printed form.  Concatenating two index ranges is
`Fin.append`, and `Fin.sum_univ_add` splits the resulting sum.

## The Leavitt case, at both of the repository's families

The repository carries two packagings of a Leavitt family: `LeavittFamily`,
the binary one presented by `(eq:leavitt)`, and `CompleteMatrixFamily A ι`, the
`ι`-ary one used for `L_k(1,m)` in `Leavitt.AryLeavitt`.  Both are covered:

* `leavittFamily_full` — for `s = s₀`, `t = t₀` the sandwich
  `t₁(1 - s₀t₀)s₁ = 1` follows from `t₁s₀ = 0` and `t₁s₁ = 1` alone; the printed
  intermediate step `1 - s₀t₀ = s₁t₁` is not needed;
* `completeMatrixFamily_full` — for any two distinct indices `i ≠ j`, with
  `s = left i`, `t = right i`, the single sandwich
  `right j · (1 - left i · right i) · left j = 1` already gives fullness.

The printed proof for `L_k(1,m)` is the second with `i = 1`, `j = 2`; the
printed intermediate identity `1 - s₁t₁ = ∑_{i≥2} sᵢtᵢ` is not needed, since
the sandwich is checked directly from the two relations.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRing

open scoped BigOperators

/-! ## The printed fullness condition -/

section Simple

variable {R : Type*} [Ring R]

/-- The set of finite sums `∑_k a_k e b_k` — the printed gloss of the
two-sided ideal `R e R`. -/
private def fullSums (e : R) : Set R :=
  {y | ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * e * b k = y}

private theorem fullSums_zero (e : R) : (0 : R) ∈ fullSums e :=
  ⟨0, Fin.elim0, Fin.elim0, by simp⟩

private theorem fullSums_add {e x y : R} (hx : x ∈ fullSums e)
    (hy : y ∈ fullSums e) : x + y ∈ fullSums e := by
  obtain ⟨m, a, b, hab⟩ := hx
  obtain ⟨m', a', b', hab'⟩ := hy
  refine ⟨m + m', Fin.append a a', Fin.append b b', ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [hab, hab']

private theorem fullSums_neg {e x : R} (hx : x ∈ fullSums e) :
    -x ∈ fullSums e := by
  obtain ⟨m, a, b, hab⟩ := hx
  refine ⟨m, fun k ↦ -a k, b, ?_⟩
  rw [← hab, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [neg_mul, neg_mul]

private theorem fullSums_mul_left {e x y : R} (hy : y ∈ fullSums e) :
    x * y ∈ fullSums e := by
  obtain ⟨m, a, b, hab⟩ := hy
  refine ⟨m, fun k ↦ x * a k, b, ?_⟩
  rw [← hab, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by simp only [mul_assoc]

private theorem fullSums_mul_right {e x y : R} (hx : x ∈ fullSums e) :
    x * y ∈ fullSums e := by
  obtain ⟨m, a, b, hab⟩ := hx
  refine ⟨m, a, fun k ↦ b k * y, ?_⟩
  rw [← hab, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by simp only [mul_assoc]

/-- The finite sums `∑_k a_k e b_k` form a two-sided ideal — the printed
`R e R`, in the printed indexed-sum form. -/
private def fullIdeal (e : R) : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' (fullSums e) (fullSums_zero e) fullSums_add fullSums_neg
    fullSums_mul_left fullSums_mul_right

private theorem mem_fullIdeal {e x : R} : x ∈ fullIdeal e ↔ x ∈ fullSums e := by
  simp [fullIdeal]

/-- **In a simple ring every nonzero element is full.**  This is the printed
sentence "since `R` is simple it generates `R` as a two-sided ideal", written
out in the form `∑_j a_j e b_j = 1` that the manuscript itself gives for the
ideal condition.  Idempotence of `e` is not used. -/
theorem exists_sum_eq_one_of_isSimpleRing [IsSimpleRing R] {e : R}
    (he : e ≠ 0) :
    ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * e * b k = 1 := by
  have hmem : e ∈ fullIdeal e :=
    mem_fullIdeal.mpr ⟨1, fun _ ↦ 1, fun _ ↦ 1, by simp⟩
  have hone : (1 : R) ∈ fullIdeal e :=
    IsSimpleRing.one_mem_of_ne_zero_mem (fullIdeal e) he hmem
  exact mem_fullIdeal.mp hone

/-- **The printed hypothesis of `thm:full-defect-ring` in a simple ring that is
not directly finite.**  From a one-sided inverse pair `ts = 1 ≠ st` the
complementary idempotent `1 - st` is nonzero, so it is full. -/
theorem isSimpleRing_full_of_not_directlyFinite [IsSimpleRing R] {s t : R}
    (hts : t * s = 1) (hst : s * t ≠ 1) :
    t * s = 1 ∧
      ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1 := by
  refine ⟨hts, exists_sum_eq_one_of_isSimpleRing ?_⟩
  exact sub_ne_zero_of_ne fun h ↦ hst h.symm

end Simple

/-! ## The Leavitt families of the repository -/

section Leavitt

variable {A : Type*} [Ring A]

/-- **The binary Leavitt family satisfies the printed hypothesis.**  With
`s = s₀` and `t = t₀`, the relation `t₀s₀ = 1` is one of `(eq:leavitt)`, and the
single sandwich `t₁(1 - s₀t₀)s₁ = 1` gives fullness, because `t₁s₀ = 0` and
`t₁s₁ = 1`.  The printed intermediate step `1 - s₀t₀ = s₁t₁` — which needs the
completeness relation `s₀t₀ + s₁t₁ = 1` — is not used. -/
theorem leavittFamily_full (L : LeavittFamily A) :
    L.t0 * L.s0 = 1 ∧
      ∃ (m : ℕ) (a b : Fin m → A),
        ∑ k, a k * (1 - L.s0 * L.t0) * b k = 1 := by
  refine ⟨L.t0_s0, 1, fun _ ↦ L.t1, fun _ ↦ L.s1, ?_⟩
  have key : L.t1 * (1 - L.s0 * L.t0) = L.t1 := by
    rw [mul_sub, mul_one, ← mul_assoc, L.t1_s0, zero_mul, sub_zero]
  rw [Fin.sum_univ_one, key, L.t1_s1]

/-- **Every `ι`-ary Leavitt family with two distinct indices satisfies the
printed hypothesis.**  With `s = left i` and `t = right i`, the relation
`right i · left i = 1` is `tᵢsᵢ = 1`, and for any second index `j ≠ i` the
single sandwich `right j · (1 - left i · right i) · left j = 1` gives fullness,
because `right j · left i = 0`.

This is the printed Leavitt case of `cor:simple-infinite-ring`, at `i = 1`,
`j = 2`; the printed intermediate identity `1 - s₁t₁ = ∑_{i≥2}s_it_i` is not
needed. -/
theorem completeMatrixFamily_full {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : CompleteMatrixFamily A ι) {i j : ι} (hij : i ≠ j) :
    F.right i * F.left i = 1 ∧
      ∃ (m : ℕ) (a b : Fin m → A),
        ∑ k, a k * (1 - F.left i * F.right i) * b k = 1 := by
  have hii : F.right i * F.left i = 1 := by
    rw [F.orthogonal i i, if_pos rfl]
  have hjj : F.right j * F.left j = 1 := by
    rw [F.orthogonal j j, if_pos rfl]
  have hji : F.right j * F.left i = 0 := by
    rw [F.orthogonal j i, if_neg (Ne.symm hij)]
  refine ⟨hii, 1, fun _ ↦ F.right j, fun _ ↦ F.left j, ?_⟩
  have key : F.right j * (1 - F.left i * F.right i) = F.right j := by
    rw [mul_sub, mul_one, ← mul_assoc, hji, zero_mul, sub_zero]
  rw [Fin.sum_univ_one, key, hjj]

end Leavitt

end FullDefectRing
end OneSidedMFRadical
end Manuscript
end GroupApproximation
