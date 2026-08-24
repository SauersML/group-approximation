import GroupApproximation.Leavitt.ElementaryNormalGeneration

/-!
# Extracting an elementary transvection from a noncentral normal element

`ElementaryNormalGeneration` proves that a normal subgroup of `EL_ι(R)` which
contains *one* elementary root `e_{ij}(x)` with a unit sandwich `a x b = 1` is
already everything.  What that file does not supply is the step which produces
the elementary root in the first place: Proposition `prop:simple` of the
manuscript needs

> **(P)** if a normal subgroup `N ⊴ EL_ι(R)` contains an element which is not
> central in `GL_ι(R)`, then `N` contains a nontrivial elementary transvection.

This file develops the group- and matrix-theoretic calculus behind (P) and
proves the statement in the two structurally distinct configurations that the
classical argument distinguishes.  Everything below is over an arbitrary unital
ring and an arbitrary finite index type; nothing is specific to Leavitt
algebras.

## What is proved

* **Square-zero calculus.**  `sqZeroUnit A hA` is the unipotent `1 + A` attached
  to a square-zero matrix.  `unipotent_commutator` computes
  `⁅1 + A, 1 + B⁆ = 1 + AB - BA + BAB - ABA + ABAB`, and the two one-sided
  degenerations `unipotent_commutator_of_left_annihilates` (`AB = 0`, `1 - BA`) and
  `unipotent_commutator_of_right_annihilates` (`BA = 0`, `1 + AB`) are the engine of
  the whole file.
* **Conjugation.**  `conj_elementaryUnit` identifies `u e_{ij}(a) u⁻¹` with
  `1 + u E_{ij}(a) u⁻¹`, `conjSingle_apply` gives the entry formula
  `(u E_{ij}(a) u⁻¹)_{pq} = u_{pi} a (u⁻¹)_{jq}`, and `conjSingle_mul_self` records
  that this rank-one matrix squares to zero as soon as `i ≠ j`.
* **Row extraction.**  `row_supported_commutator`: if `v` is supported in one row
  `k` and `v_{kk} = 0`, then `⁅1 + v, e_{mn}(c)⁆ = e_{kn}(v_{km} c)` for `m, n ≠ k`,
  `m ≠ n` — a *genuine* transvection, not merely a product of transvections.
  This is the mechanism that turns a "one-row unipotent" living in `N` into an
  elementary generator living in `N`.
* **Supply of one-row unipotents.**  `commutator_conj_mem` is the purely
  group-theoretic remark that `⁅g e g⁻¹, f⁆ ∈ N` whenever `g ∈ N ⊴ G` and `e`
  commutes with `f`; combined with the square-zero calculus this puts a large
  family of explicitly computed matrices inside `N`.
* **(P) in two configurations.**
  `exists_elGen_mem_of_conjSingle_eq` settles the case in which conjugation by
  `g` preserves the line of `E_{ij}`: the commutator `⁅g, e_{ij}(a)⁆` is then
  *literally* a transvection.  In particular this covers every invertible
  diagonal `g` (`conjSingle_eq_single_of_concentrated`), which is the classical
  "case (ii)".
  `exists_elGen_mem_of_inv_entry_zero` settles the configuration in which some
  off-diagonal entry of `g⁻¹` vanishes while the matching entry of `g` does not:
  a double commutator is then a one-row unipotent and row extraction applies.
* **Noncentrality is a statement about elementary matrices.**
  `commute_of_forall_single`: a matrix commuting with every `E_{ij}(a)`, `i ≠ j`,
  is a central scalar and therefore commutes with everything.  Hence a `g` which
  is not central in `GL_ι(R)` fails to commute with some `E_{ij}(a)`
  (`exists_noncommuting_single_of_not_central`), which is the hypothesis the two
  configurations above consume.

## What is *not* proved

The remaining configuration is the one in which `g` has a nonzero off-diagonal
entry but neither `g` nor `g⁻¹` has any zero entry at a usable position.  The
double commutator `⁅g e_{ij}(a) g⁻¹, e_{kl}(b)⁆` is then the full six-term
expression of `unipotent_commutator` with both `(g⁻¹)_{jk}` and `g_{li}` nonzero,
and it is neither row- nor column-supported; the classical treatment passes
through the level ideal of `g` rather than through a single commutator.  No
statement about that configuration is asserted here.
-/

namespace GroupApproximation

open scoped BigOperators commutatorElement

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-! ### Entry formulas for single-entry matrices

Both helpers are the rank-one bookkeeping that every computation below runs on:
right multiplication by `E_{ij}(a)` reads off column `i`, left multiplication
reads off row `j`. -/

theorem matrix_mul_single_apply (M : Matrix ι ι R) (i j : ι) (a : R) (p q : ι) :
    (M * Matrix.single i j a) p q = if q = j then M p i * a else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hqj : q = j
  · rw [if_pos hqj, Finset.sum_eq_single i]
    · rw [Matrix.single_apply, if_pos ⟨rfl, hqj.symm⟩]
    · intro k _ hki
      rw [Matrix.single_apply, if_neg fun h => hki h.1.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [if_neg hqj]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.single_apply, if_neg fun h => hqj h.2.symm, mul_zero]

theorem matrix_single_mul_apply (i j : ι) (a : R) (M : Matrix ι ι R) (p q : ι) :
    (Matrix.single i j a * M) p q = if p = i then a * M j q else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hpi : p = i
  · rw [if_pos hpi, Finset.sum_eq_single j]
    · rw [Matrix.single_apply, if_pos ⟨hpi.symm, rfl⟩]
    · intro k _ hkj
      rw [Matrix.single_apply, if_neg fun h => hkj h.2.symm, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · rw [if_neg hpi]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.single_apply, if_neg fun h => hpi h.1.symm, zero_mul]

omit [Fintype ι] in
/-- `E_{ij}` is additive in its coefficient, in the subtracted form needed to
recognise a difference of two conjugate roots as a single root. -/
theorem matrix_single_sub (i j : ι) (x y : R) :
    Matrix.single i j (x - y) =
      (Matrix.single i j x : Matrix ι ι R) - Matrix.single i j y := by
  ext p q
  rw [Matrix.sub_apply, Matrix.single_apply, Matrix.single_apply,
    Matrix.single_apply]
  split_ifs
  · rfl
  · rw [sub_zero]

/-! ### Square-zero unipotents

Every matrix appearing in the extraction argument is `1 + A` with `A * A = 0`:
single-entry matrices, their conjugates, and one-row matrices with a vanishing
diagonal entry all have this shape, and the shape is exactly what makes the
inverse explicit and the commutator finite. -/

/-- The unipotent `1 + A` attached to a square-zero matrix, with its inverse
`1 - A` written out. -/
def sqZeroUnit (A : Matrix ι ι R) (hA : A * A = 0) : (Matrix ι ι R)ˣ where
  val := 1 + A
  inv := 1 - A
  val_inv := by
    have e : (1 + A) * (1 - A) = 1 - A * A := by noncomm_ring
    rw [e, hA, sub_zero]
  inv_val := by
    have e : (1 - A) * (1 + A) = 1 - A * A := by noncomm_ring
    rw [e, hA, sub_zero]

@[simp] theorem sqZeroUnit_val (A : Matrix ι ι R) (hA : A * A = 0) :
    (sqZeroUnit A hA : Matrix ι ι R) = 1 + A := rfl

/-- The elementary root matrix is the square-zero unipotent of its single-entry
matrix. -/
theorem elementaryUnit_eq_sqZeroUnit (i j : ι) (h : i ≠ j) (a : R) :
    elementaryUnit i j h a =
      sqZeroUnit (Matrix.single i j a) (single_mul_self_eq_zero i j h a) := rfl

/-- **The commutator of two square-zero unipotents.**  Six terms survive.

The identity is stated on the underlying matrix products rather than on
`⁅sqZeroUnit A hA, sqZeroUnit B hB⁆`: the coercion of a bracket to the base ring
would have to be written `(⁅x, y⁆ : (Matrix ι ι R)ˣ)`, and giving `⁅x, y⁆` an
expected type forces instance search for `Bracket ?L ((Matrix ι ι R)ˣ)` with `?L`
still unknown.  Every user below reaches this form through `Units.ext` and a
`show`, for which the two are definitionally equal. -/
theorem unipotent_commutator (A B : Matrix ι ι R) (hA : A * A = 0)
    (hB : B * B = 0) :
    (1 + A) * (1 + B) * (1 - A) * (1 - B) =
      1 + A * B - B * A + B * A * B - A * B * A + A * B * A * B := by
  have e : (1 + A) * (1 + B) * (1 - A) * (1 - B)
      = 1 + A * B - B * A + B * A * B - A * B * A + A * B * A * B
        - A * A + A * A * B - B * B - A * (B * B) := by noncomm_ring
  rw [e, hA, hB]
  simp

/-- **Left degeneration.**  When `A` annihilates `B` on the left the commutator
collapses to the single term `1 - BA`. -/
theorem unipotent_commutator_of_left_annihilates (A B : Matrix ι ι R)
    (hA : A * A = 0) (hB : B * B = 0) (hAB : A * B = 0) :
    (1 + A) * (1 + B) * (1 - A) * (1 - B) = 1 - B * A := by
  have e : (1 + A) * (1 + B) * (1 - A) * (1 - B)
      = 1 - B * A + A * B - A * A + A * A * B - B * B + B * (A * B)
        - A * B * A - A * B * B + A * B * A * B := by noncomm_ring
  rw [e, hA, hB, hAB]
  simp

/-- **Right degeneration.**  When `B` annihilates `A` on the left the commutator
collapses to the single term `1 + AB`. -/
theorem unipotent_commutator_of_right_annihilates (A B : Matrix ι ι R)
    (hA : A * A = 0) (hB : B * B = 0) (hBA : B * A = 0) :
    (1 + A) * (1 + B) * (1 - A) * (1 - B) = 1 + A * B := by
  have e : (1 + A) * (1 + B) * (1 - A) * (1 - B)
      = 1 + A * B - A * A + A * A * B - B * A - B * B + B * A * B
        - A * (B * A) - A * (B * B) + A * (B * A) * B := by noncomm_ring
  rw [e, hA, hB, hBA]
  simp

omit [DecidableEq ι] in
/-- The one-row defect produced by the left degeneration squares to zero:
`(BA)(BA) = B(AB)A`. -/
theorem neg_mul_sq_eq_zero_of_left_annihilates (A B : Matrix ι ι R)
    (hAB : A * B = 0) : (-(B * A)) * (-(B * A)) = 0 := by
  have e : (-(B * A)) * (-(B * A)) = B * (A * B) * A := by
    rw [neg_mul_neg, mul_assoc B A (B * A), ← mul_assoc A B A,
      ← mul_assoc B (A * B) A]
  rw [e, hAB, mul_zero, zero_mul]

/-! ### Conjugating an elementary root

Conjugation by a unit turns the single-entry matrix `E_{ij}(a)` into the rank-one
matrix with column `u_{*i}`, coefficient `a` and row `(u⁻¹)_{j*}`; the vanishing
`(u⁻¹ u)_{ji} = 0` for `i ≠ j` is what makes it square to zero. -/

/-- The conjugate `u E_{ij}(a) u⁻¹` of a single-entry matrix. -/
def conjSingle (u : (Matrix ι ι R)ˣ) (i j : ι) (a : R) : Matrix ι ι R :=
  (u : Matrix ι ι R) * Matrix.single i j a * ((u⁻¹ : (Matrix ι ι R)ˣ) :
    Matrix ι ι R)

/-- **The entry formula.**  This is the pure linear algebra underlying every
commutator computation in the file. -/
theorem conjSingle_apply (u : (Matrix ι ι R)ˣ) (i j : ι) (a : R) (p q : ι) :
    conjSingle u i j a p q =
      (u : Matrix ι ι R) p i * a *
        ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j q := by
  classical
  show ((u : Matrix ι ι R) * Matrix.single i j a *
    ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) p q = _
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [matrix_mul_single_apply, if_pos rfl]
  · intro l _ hl
    rw [matrix_mul_single_apply, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The conjugate of a single-entry matrix off the diagonal squares to zero. -/
theorem conjSingle_mul_self (u : (Matrix ι ι R)ˣ) (i j : ι) (h : i ≠ j) (a : R) :
    conjSingle u i j a * conjSingle u i j a = 0 := by
  have hvu : ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) * (u : Matrix ι ι R) = 1 :=
    u.inv_mul
  have hx := single_mul_self_eq_zero i j h a
  show ((u : Matrix ι ι R) * Matrix.single i j a *
      ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) *
    ((u : Matrix ι ι R) * Matrix.single i j a *
      ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) = 0
  have key : ((u : Matrix ι ι R) * Matrix.single i j a *
        ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) *
      ((u : Matrix ι ι R) * Matrix.single i j a *
        ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R))
      = (u : Matrix ι ι R) *
          (Matrix.single i j a *
            ((((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) * (u : Matrix ι ι R)) *
              Matrix.single i j a)) *
          ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) := by
    noncomm_ring
  rw [key, hvu, one_mul, hx, mul_zero, zero_mul]

/-- **The conjugation formula.**  `u e_{ij}(a) u⁻¹ = 1 + u E_{ij}(a) u⁻¹`. -/
theorem conj_elementaryUnit (u : (Matrix ι ι R)ˣ) (i j : ι) (h : i ≠ j) (a : R) :
    u * elementaryUnit i j h a * u⁻¹ =
      sqZeroUnit (conjSingle u i j a) (conjSingle_mul_self u i j h a) := by
  apply Units.ext
  have huv : (u : Matrix ι ι R) * ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) = 1 :=
    u.mul_inv
  show (u : Matrix ι ι R) * (1 + Matrix.single i j a) *
      ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)
    = 1 + (u : Matrix ι ι R) * Matrix.single i j a *
        ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)
  have e : (u : Matrix ι ι R) * (1 + Matrix.single i j a) *
        ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = (u : Matrix ι ι R) * ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)
        + (u : Matrix ι ι R) * Matrix.single i j a *
            ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) := by
    noncomm_ring
  rw [e, huv]

/-- Conjugation preserves the line of `E_{ij}` exactly when column `i` of `u` and
row `j` of `u⁻¹` are concentrated on the diagonal.  Every invertible diagonal
matrix satisfies this, which is the classical "diagonal" configuration. -/
theorem conjSingle_eq_single_of_concentrated (u : (Matrix ι ι R)ˣ) (i j : ι)
    (a : R)
    (hcol : ∀ p : ι, p ≠ i → (u : Matrix ι ι R) p i = 0)
    (hrow : ∀ q : ι, q ≠ j →
      ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j q = 0) :
    conjSingle u i j a =
      Matrix.single i j ((u : Matrix ι ι R) i i * a *
        ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j j) := by
  ext p q
  rw [conjSingle_apply, Matrix.single_apply]
  by_cases hp : p = i
  · by_cases hq : q = j
    · rw [if_pos ⟨hp.symm, hq.symm⟩, hp, hq]
    · rw [if_neg fun hh => hq hh.2.symm, hrow q hq, mul_zero]
  · rw [if_neg fun hh => hp hh.1.symm, hcol p hp, zero_mul, zero_mul]

/-! ### One-row unipotents

The matrices that the extraction argument actually produces inside `N` are not
elementary; they are unipotents `1 + v` whose defect `v` lives in a single row
and vanishes on the diagonal of that row.  Such a `v` squares to zero, and one
further commutator with an elementary matrix *away from that row* collapses the
whole unipotent to a single transvection. -/

/-- `v` is supported in row `k`. -/
def IsRowSupported (v : Matrix ι ι R) (k : ι) : Prop :=
  ∀ s t : ι, s ≠ k → v s t = 0

theorem IsRowSupported.mul_self {v : Matrix ι ι R} {k : ι}
    (hv : IsRowSupported v k) (hd : v k k = 0) : v * v = 0 := by
  classical
  ext s t
  rw [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hs : s = k
  · refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : m = k
    · rw [hs, hm, hd, zero_mul]
    · rw [hv m t hm, mul_zero]
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [hv s m hs, zero_mul]

/-- A one-row matrix multiplied on the right by a single-entry matrix is again a
single-entry matrix — this is the collapse that produces a genuine transvection
rather than a product of transvections. -/
theorem row_mul_single (v : Matrix ι ι R) {k : ι} (hv : IsRowSupported v k)
    (m n : ι) (c : R) :
    v * Matrix.single m n c = Matrix.single k n (v k m * c) := by
  classical
  ext p q
  rw [matrix_mul_single_apply, Matrix.single_apply]
  by_cases hq : q = n
  · by_cases hp : p = k
    · rw [if_pos hq, if_pos ⟨hp.symm, hq.symm⟩, hp]
    · rw [if_pos hq, if_neg fun hh => hp hh.1.symm, hv p m hp, zero_mul]
  · rw [if_neg hq, if_neg fun hh => hq hh.2.symm]

/-- A single-entry matrix whose *column* index avoids the supported row
annihilates a one-row matrix on the left. -/
theorem single_mul_row_eq_zero (v : Matrix ι ι R) {k : ι}
    (hv : IsRowSupported v k) {m n : ι} (hnk : n ≠ k) (c : R) :
    Matrix.single m n c * v = 0 := by
  classical
  ext s t
  rw [matrix_single_mul_apply, Matrix.zero_apply]
  by_cases hs : s = m
  · rw [if_pos hs, hv n t hnk, mul_zero]
  · rw [if_neg hs]

/-- **Row extraction.**  A one-row unipotent with vanishing diagonal entry yields
a *single* elementary transvection after one commutator with an elementary matrix
whose two indices both avoid the supported row. -/
theorem row_supported_commutator (v : Matrix ι ι R) {k : ι}
    (hv : IsRowSupported v k) (hd : v k k = 0) {m n : ι}
    (hnk : n ≠ k) (hmn : m ≠ n) (c : R) :
    ⁅sqZeroUnit v (hv.mul_self hd), elementaryUnit m n hmn c⁆
      = elementaryUnit k n (Ne.symm hnk) (v k m * c) := by
  apply Units.ext
  have hBA : Matrix.single m n c * v = 0 := single_mul_row_eq_zero v hv hnk c
  show (1 + v) * (1 + Matrix.single m n c) * (1 - v) *
      (1 - Matrix.single m n c) = 1 + Matrix.single k n (v k m * c)
  rw [unipotent_commutator_of_right_annihilates v (Matrix.single m n c)
      (hv.mul_self hd) (single_mul_self_eq_zero m n hmn c) hBA,
    row_mul_single v hv m n c]

theorem isRowSupported_single_mul (M : Matrix ι ι R) (k l : ι) (b : R) :
    IsRowSupported (-(Matrix.single k l b * M)) k := by
  intro s t hs
  rw [Matrix.neg_apply, matrix_single_mul_apply, if_neg hs, neg_zero]

/-! ### The group-theoretic supply of elements of `N` -/

/-- A commutator with a left entry in a normal subgroup lies in that subgroup. -/
theorem commutator_mem_left {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]
    {x : G} (hx : x ∈ N) (y : G) : ⁅x, y⁆ ∈ N := by
  have h : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
    rw [commutatorElement_def, mul_assoc x y x⁻¹, mul_assoc x (y * x⁻¹) y⁻¹]
  rw [h]
  exact N.mul_mem hx (hN.conj_mem x⁻¹ (N.inv_mem hx) y)

/-- **The supply lemma.**  If `g` lies in a normal subgroup and `e` commutes with
`f`, then `⁅g e g⁻¹, f⁆` lies in that subgroup — even though `g e g⁻¹` itself
does not.  Modulo `N` the conjugate `g e g⁻¹` is just `e`, and `⁅e, f⁆ = 1`. -/
theorem commutator_conj_mem {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {g : G} (hg : g ∈ N) (e f : G) (hef : e * f = f * e) :
    ⁅g * e * g⁻¹, f⁆ ∈ N := by
  have hg1 : (QuotientGroup.mk' N) g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  have hx : (QuotientGroup.mk' N) (g * e * g⁻¹) = (QuotientGroup.mk' N) e := by
    rw [map_mul, map_mul, map_inv, hg1, one_mul, inv_one, mul_one]
  have hcomm : (QuotientGroup.mk' N) e * (QuotientGroup.mk' N) f
      = (QuotientGroup.mk' N) f * (QuotientGroup.mk' N) e := by
    rw [← map_mul, ← map_mul, hef]
  refine (QuotientGroup.eq_one_iff _).mp ?_
  show (QuotientGroup.mk' N) ⁅g * e * g⁻¹, f⁆ = 1
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hx,
    hcomm, mul_inv_cancel_right, mul_inv_cancel]

/-- Two elementary roots commute as soon as neither one's target index is the
other's source index. -/
theorem elGen_commute {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    elGen i j hij a * elGen k l hkl b = elGen k l hkl b * elGen i j hij a := by
  apply Subtype.ext
  apply Units.ext
  have h1 : Matrix.single i j a * Matrix.single k l b = (0 : Matrix ι ι R) :=
    Matrix.single_mul_single_of_ne (c := a) i j k hjk b
  have h2 : Matrix.single k l b * Matrix.single i j a = (0 : Matrix ι ι R) :=
    Matrix.single_mul_single_of_ne (c := b) k l i hli a
  show (1 + Matrix.single i j a) * (1 + Matrix.single k l b)
      = (1 + Matrix.single k l b) * (1 + Matrix.single i j a)
  have e1 : (1 + Matrix.single i j a) * (1 + Matrix.single k l b)
      = 1 + Matrix.single i j a + Matrix.single k l b
        + Matrix.single i j a * Matrix.single k l b := by noncomm_ring
  have e2 : (1 + Matrix.single k l b) * (1 + Matrix.single i j a)
      = 1 + Matrix.single k l b + Matrix.single i j a
        + Matrix.single k l b * Matrix.single i j a := by noncomm_ring
  rw [e1, e2, h1, h2, add_zero, add_zero, add_right_comm]

/-- **The double commutator lies in `N`.**  `g ∈ N`, the two roots commute, and
the conjugate `g e_{ij}(a) g⁻¹` — which is not itself in `N` — is nevertheless
harmless once commutated with the second root. -/
theorem doubleCommutator_mem (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (a b : R) :
    ⁅g * elGen i j hij a * g⁻¹, elGen k l hkl b⁆ ∈ N :=
  commutator_conj_mem N hg _ _ (elGen_commute hij hkl hjk hli a b)

/-- **The double commutator, computed.**  When the conjugated root annihilates
the second root on the left, five of the six terms of `unipotent_commutator`
vanish and what is left is a one-row unipotent.  Stated as an equation between
units, so that no bracket ever carries an expected type. -/
theorem doubleCommutator_eq_sqZeroUnit (u : (Matrix ι ι R)ˣ) {i j k l : ι}
    (hij : i ≠ j) (hkl : k ≠ l) (a b : R)
    (hAB : conjSingle u i j a * Matrix.single k l b = 0) :
    ⁅u * elementaryUnit i j hij a * u⁻¹, elementaryUnit k l hkl b⁆
      = sqZeroUnit (-(Matrix.single k l b * conjSingle u i j a))
          (neg_mul_sq_eq_zero_of_left_annihilates (conjSingle u i j a)
            (Matrix.single k l b) hAB) := by
  rw [conj_elementaryUnit u i j hij a, elementaryUnit_eq_sqZeroUnit k l hkl b]
  apply Units.ext
  show (1 + conjSingle u i j a) * (1 + Matrix.single k l b) *
      (1 - conjSingle u i j a) * (1 - Matrix.single k l b)
    = 1 + -(Matrix.single k l b * conjSingle u i j a)
  rw [unipotent_commutator_of_left_annihilates (conjSingle u i j a)
      (Matrix.single k l b) (conjSingle_mul_self u i j hij a)
      (single_mul_self_eq_zero k l hkl b) hAB, sub_eq_add_neg]

/-! ### Configuration 1: conjugation preserves the line of `E_{ij}`

If `g E_{ij}(a) g⁻¹` is again a multiple of `E_{ij}`, then `⁅g, e_{ij}(a)⁆` is
*literally* an elementary transvection and no commutator gymnastics is needed.
Every invertible diagonal `g` falls under this heading, by
`conjSingle_eq_single_of_concentrated`; this is the classical case in which `g`
is diagonal but either has two different diagonal entries or a diagonal entry
which is not central. -/

theorem commutator_eq_elementaryUnit_of_conjSingle (u : (Matrix ι ι R)ˣ)
    {i j : ι} (hij : i ≠ j) (a y : R)
    (hconj : conjSingle u i j a = Matrix.single i j y) :
    ⁅u, elementaryUnit i j hij a⁆ = elementaryUnit i j hij (y - a) := by
  have hz : Matrix.single i j y * Matrix.single i j a = (0 : Matrix ι ι R) :=
    Matrix.single_mul_single_of_ne (c := y) i j i hij.symm a
  have e1 : (1 + Matrix.single i j y) * (1 - Matrix.single i j a)
      = 1 + (Matrix.single i j y - Matrix.single i j a)
        - Matrix.single i j y * Matrix.single i j a := by noncomm_ring
  have key : ⁅u, elementaryUnit i j hij a⁆
      = u * elementaryUnit i j hij a * u⁻¹ * (elementaryUnit i j hij a)⁻¹ := rfl
  rw [key, conj_elementaryUnit u i j hij a]
  apply Units.ext
  show (1 + conjSingle u i j a) * (1 - Matrix.single i j a)
      = 1 + Matrix.single i j (y - a)
  rw [hconj, e1, hz, sub_zero, matrix_single_sub]

/-- **(P) in the line-preserving configuration.**  A normal subgroup containing a
`g` whose conjugation multiplies `E_{ij}(a)` by a *different* coefficient already
contains a nontrivial elementary transvection. -/
theorem exists_elGen_mem_of_conjSingle_eq
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N) {i j : ι} (hij : i ≠ j) {a y : R}
    (hconj : conjSingle (g : (Matrix ι ι R)ˣ) i j a = Matrix.single i j y)
    (hne : y ≠ a) :
    ∃ (p q : ι) (hpq : p ≠ q) (x : R), x ≠ 0 ∧ elGen p q hpq x ∈ N := by
  refine ⟨i, j, hij, y - a, sub_ne_zero.mpr hne, ?_⟩
  have hmem : ⁅g, elGen i j hij a⁆ ∈ N := commutator_mem_left N hg _
  have heq : ⁅g, elGen i j hij a⁆ = elGen i j hij (y - a) := by
    apply Subtype.ext
    show ⁅(g : (Matrix ι ι R)ˣ), elementaryUnit i j hij a⁆
        = elementaryUnit i j hij (y - a)
    exact commutator_eq_elementaryUnit_of_conjSingle (g : (Matrix ι ι R)ˣ) hij a y
      hconj
  rw [heq] at hmem
  exact hmem

/-! ### Configuration 2: a vanishing entry of `g⁻¹` -/

/-- A nonzero entry of `u` is never annihilated by the whole of the matching row
of `u⁻¹`: the identity `(u⁻¹ u)_{jj} = 1` forbids it. -/
theorem exists_mul_inv_entry_ne_zero (u : (Matrix ι ι R)ˣ) (j k : ι)
    (hne : (u : Matrix ι ι R) j k ≠ 0) :
    ∃ m : ι, (u : Matrix ι ι R) j k *
      ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j m ≠ 0 := by
  classical
  by_contra hcon
  apply hne
  have hall : ∀ m : ι, (u : Matrix ι ι R) j k *
      ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j m = 0 := by
    intro m
    by_contra hm
    exact hcon ⟨m, hm⟩
  have hjj : ∑ m : ι, ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j m *
      (u : Matrix ι ι R) m j = 1 := by
    have h : (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) *
        (u : Matrix ι ι R)) j j = (1 : Matrix ι ι R) j j := by
      rw [u.inv_mul]
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    exact h
  calc (u : Matrix ι ι R) j k
      = (u : Matrix ι ι R) j k * 1 := (mul_one _).symm
    _ = ∑ m : ι, (u : Matrix ι ι R) j k *
          (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j m *
            (u : Matrix ι ι R) m j) := by rw [← hjj, Finset.mul_sum]
    _ = 0 := by
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [← mul_assoc, hall m, zero_mul]

/-- **Row extraction inside a normal subgroup.**  An element of `N` which, as a
matrix, is a one-row unipotent with a nonzero entry off the diagonal hands over a
nontrivial elementary root of `N`. -/
theorem exists_elGen_mem_of_row_supported (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {z : elementaryGroup ι R} (hz : z ∈ N) {v : Matrix ι ι R} {k : ι}
    (hv : IsRowSupported v k) (hd : v k k = 0)
    (hzv : (z : (Matrix ι ι R)ˣ) = sqZeroUnit v (hv.mul_self hd))
    {m : ι} (hvm : v k m ≠ 0) :
    ∃ (p q : ι) (hpq : p ≠ q) (x : R), x ≠ 0 ∧ elGen p q hpq x ∈ N := by
  obtain ⟨n, hnk, hnm⟩ := exists_third_index hcard k m
  refine ⟨k, n, Ne.symm hnk, v k m * 1, ?_, ?_⟩
  · rw [mul_one]
    exact hvm
  · have hmem : ⁅z, elGen m n (Ne.symm hnm) (1 : R)⁆ ∈ N :=
      commutator_mem_left N hz _
    have heq : ⁅z, elGen m n (Ne.symm hnm) (1 : R)⁆
        = elGen k n (Ne.symm hnk) (v k m * 1) := by
      apply Subtype.ext
      show ⁅(z : (Matrix ι ι R)ˣ), elementaryUnit m n (Ne.symm hnm) (1 : R)⁆
          = elementaryUnit k n (Ne.symm hnk) (v k m * 1)
      rw [hzv]
      exact row_supported_commutator v hv hd hnk (Ne.symm hnm) 1
    rw [heq] at hmem
    exact hmem

/-- **(P) in the vanishing-entry configuration.**  If `N` contains a `g` for which
some off-diagonal entry of `g⁻¹` vanishes while the *same* entry of `g` does not,
then `N` contains a nontrivial elementary transvection.

The proof is one double commutator with the two roots `e_{kj}(1)` and `e_{kj}(1)`
— which commute — followed by row extraction. -/
theorem exists_elGen_mem_of_inv_entry_zero (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N) {j k : ι} (hjk : j ≠ k)
    (hzero : (((g : (Matrix ι ι R)ˣ)⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j k = 0)
    (hne : ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) j k ≠ 0) :
    ∃ (p q : ι) (hpq : p ≠ q) (x : R), x ≠ 0 ∧ elGen p q hpq x ∈ N := by
  classical
  have hkj : k ≠ j := Ne.symm hjk
  have hAB : conjSingle (g : (Matrix ι ι R)ˣ) k j (1 : R) *
      Matrix.single k j (1 : R) = 0 := by
    ext s t
    rw [matrix_mul_single_apply, Matrix.zero_apply]
    by_cases ht : t = j
    · rw [if_pos ht, conjSingle_apply, hzero, mul_zero, zero_mul]
    · rw [if_neg ht]
  obtain ⟨z, hzdef⟩ :
      ∃ z, z = ⁅g * elGen k j hkj (1 : R) * g⁻¹, elGen k j hkj (1 : R)⁆ :=
    ⟨_, rfl⟩
  have hz : z ∈ N := by
    rw [hzdef]
    exact doubleCommutator_mem N hg hkj hkj hjk hjk 1 1
  have hzv : (z : (Matrix ι ι R)ˣ) =
      sqZeroUnit (-(Matrix.single k j (1 : R) *
          conjSingle (g : (Matrix ι ι R)ˣ) k j (1 : R)))
        (neg_mul_sq_eq_zero_of_left_annihilates
          (conjSingle (g : (Matrix ι ι R)ˣ) k j (1 : R))
          (Matrix.single k j (1 : R)) hAB) := by
    rw [hzdef]
    exact doubleCommutator_eq_sqZeroUnit (g : (Matrix ι ι R)ˣ) hkj hkj 1 1 hAB
  have hrow : IsRowSupported (-(Matrix.single k j (1 : R) *
      conjSingle (g : (Matrix ι ι R)ˣ) k j (1 : R))) k :=
    isRowSupported_single_mul _ k j 1
  have hdiag : (-(Matrix.single k j (1 : R) *
      conjSingle (g : (Matrix ι ι R)ˣ) k j (1 : R))) k k = 0 := by
    rw [Matrix.neg_apply, matrix_single_mul_apply, if_pos rfl, conjSingle_apply,
      hzero, mul_zero, mul_zero, neg_zero]
  obtain ⟨m, hm⟩ := exists_mul_inv_entry_ne_zero (g : (Matrix ι ι R)ˣ) j k hne
  have hvm : (-(Matrix.single k j (1 : R) *
      conjSingle (g : (Matrix ι ι R)ˣ) k j (1 : R))) k m ≠ 0 := by
    rw [Matrix.neg_apply, matrix_single_mul_apply, if_pos rfl, conjSingle_apply,
      one_mul, mul_one, neg_ne_zero]
    exact hm
  exact exists_elGen_mem_of_row_supported hcard N hz hrow hdiag hzv hvm

/-! ### Noncentrality is detected on elementary matrices

The hypothesis of (P) is "`g` is not central in `GL_ι(R)`".  The two
configurations above consume instead the statement "`g` does not commute with
some `E_{ij}(a)`, `i ≠ j`".  These are the same hypothesis: a matrix commuting
with every off-diagonal single-entry matrix is forced to be a scalar with central
coefficient, hence commutes with everything. -/

/-- A matrix commuting with every off-diagonal `E_{ij}(a)` commutes with every
matrix. -/
theorem commute_of_forall_single (hcard : 3 ≤ Fintype.card ι) (u : Matrix ι ι R)
    (h : ∀ (i j : ι), i ≠ j → ∀ a : R,
      u * Matrix.single i j a = Matrix.single i j a * u) (M : Matrix ι ι R) :
    u * M = M * u := by
  classical
  have hdiag : ∀ p q : ι, q ≠ p → u p q = 0 := by
    intro p q hqp
    obtain ⟨i, hip, -⟩ := exists_third_index hcard p p
    have hentry : (u * Matrix.single i p (1 : R)) i q =
        (Matrix.single i p (1 : R) * u) i q := by rw [h i p hip 1]
    rw [matrix_mul_single_apply, matrix_single_mul_apply, if_neg hqp, if_pos rfl,
      one_mul] at hentry
    exact hentry.symm
  have hcross : ∀ i j : ι, i ≠ j → ∀ a : R, u i i * a = a * u j j := by
    intro i j hij a
    have hentry : (u * Matrix.single i j a) i j =
        (Matrix.single i j a * u) i j := by rw [h i j hij a]
    rw [matrix_mul_single_apply, matrix_single_mul_apply, if_pos rfl,
      if_pos rfl] at hentry
    exact hentry
  have hdiagconst : ∀ p q : ι, u p p = u q q := by
    intro p q
    by_cases hpq : p = q
    · rw [hpq]
    · have hc := hcross p q hpq 1
      rw [mul_one, one_mul] at hc
      exact hc
  have hcentral : ∀ (p : ι) (a : R), u p p * a = a * u p p := by
    intro p a
    obtain ⟨i, hip, -⟩ := exists_third_index hcard p p
    have hc := hcross i p hip a
    rw [hdiagconst i p] at hc
    exact hc
  ext s t
  have hL : (u * M) s t = u s s * M s t := by
    rw [Matrix.mul_apply, Finset.sum_eq_single s]
    · intro l _ hl
      rw [hdiag s l hl, zero_mul]
    · intro hs
      exact absurd (Finset.mem_univ s) hs
  have hR : (M * u) s t = M s t * u t t := by
    rw [Matrix.mul_apply, Finset.sum_eq_single t]
    · intro l _ hl
      rw [hdiag l t (Ne.symm hl), mul_zero]
    · intro hs
      exact absurd (Finset.mem_univ t) hs
  rw [hL, hR, ← hdiagconst s t]
  exact hcentral s (M s t)

/-- **Noncentrality, transported to elementary matrices.**  A matrix which fails
to commute with *some* matrix already fails to commute with some off-diagonal
single-entry matrix. -/
theorem exists_noncommuting_single_of_not_central (hcard : 3 ≤ Fintype.card ι)
    (u : Matrix ι ι R) {M : Matrix ι ι R} (hM : u * M ≠ M * u) :
    ∃ (i j : ι) (_ : i ≠ j) (a : R),
      u * Matrix.single i j a ≠ Matrix.single i j a * u := by
  classical
  by_contra hcon
  apply hM
  refine commute_of_forall_single hcard u (fun i j hij a => ?_) M
  by_contra hne
  exact hcon ⟨i, j, hij, a, hne⟩

end GroupApproximation
