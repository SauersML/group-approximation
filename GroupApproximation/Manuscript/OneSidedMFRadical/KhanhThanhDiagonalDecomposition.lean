import GroupApproximation.KOne.DiagonalGroupNormalizer
import GroupApproximation.Manuscript.OneSidedMFRadical.LeavittKOneFormula
import GroupApproximation.Meta.AxiomGuard

/-!
# `GL_d(R) = EL_d(R) D_d(k)`: the printed Khanh--Thanh decomposition

`non_mf_groups_exist.tex`, proof of `cor:leavitt-mf-quotient`:

> Khanh--Thanh show that `GL_d(R) = EL_d(R)D_d(k)`, where `D_d(k)` is the
> abelian group of diagonal matrices with entries in `k^×`, which normalizes
> `EL_d(R)`, and that `K_1(R) ≅ k^×/(k^×)^{d-1}`.

That sentence carries four claims about `R = L_k(1,d)`.  Three of them are
proved here, unconditionally, for every field `k` and every `d ≥ 2`:

* **`D_d(k)` is abelian** --- `printedDiagonal_mul_comm`;
* **`D_d(k)` normalizes `EL_d(R)`** --- `printedDiagonal_le_normalizer`, which
  needs no hypothesis at all, not even `d ≥ 2`;
* **`GL_d(R) = EL_d(R) · D_d(R^×)`** --- `exists_elementary_mul_diagonal_ary`,
  the decomposition with the diagonal entries allowed to be arbitrary units of
  `R` rather than scalars.  This is rank-`d` Gaussian elimination over the
  purely infinite simple ring `L_k(1,d)`, so it is unconditional.

The fourth, `K_1(R) ≅ k^×/(k^×)^{d-1}`, is `LeavittKOneFormula.lean`'s subject
and is not touched here.

## The residual, with no slack in it

The distance between the third claim and the printed one is exactly the
replacement of `D_d(R^×)` by `D_d(k)`, and

    `printedKhanhThanhDecomposition_iff` :
      `PrintedKhanhThanhDecomposition k d ↔ UnstableScalarSurjective k d`

says so: the printed decomposition holds **if and only if** every diagonal
matrix over `R^×` is an elementary matrix times a scalar diagonal one.  The
forward direction is free; the backward direction is the elimination.  So
nothing is lost by attacking `UnstableScalarSurjective` instead, and nothing
weaker than it will do.

`printedKhanhThanhDecomposition_of_diagAt` reduces it further, to a statement
about a single unit of `R`: if for every `u : R^×` some scalar `a : k^×` has
`diag(u,1,…,1) · diag(a,1,…,1)^{-1}` elementary, the printed decomposition
follows.  That is the *unstable* form of `LeavittKOneFormula.ScalarSurjective`,
which that file records as open for `d ≥ 3` --- it is the same mathematical
content as the `K_1` half of the citation, not an independent gap.

## Why the `d = 2` route does not generalise

`BinaryLeavitt.elementaryGroup_eq_top` gives `GL_n(L_k(1,2)) = EL_n` at every
`n`, and it is proved by transporting the rank-two collapse along the
prefix-code self-similarity `A ≃+* M_m(A)`.  That transport is available only
because `L_k(1,2) ≅ M_2(L_k(1,2))`; at arity `d` the self-similarity is
`L_k(1,d) ≅ M_m(L_k(1,d))` for `m ≡ 1 (mod d-1)`, which never reaches `m = 2`
for `d ≥ 3`.  And the conclusion is not expected to survive either: the printed
`K_1(L_k(1,d)) ≅ k^×/(k^×)^{d-1}` is nontrivial as soon as `k^×` has an element
that is not a `(d-1)`-st power, and then `GL_d ≠ EL_d`.  (That identification is
the cited half and is not proved anywhere on the tree, so this paragraph is
orientation, not a theorem.)  The rank-`d` elimination of
`KOne/RankNElimination.lean` is the route that does generalise, and it is what
the statements below use.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace KhanhThanhDiagonal

open AryLeavitt RankNElimination

variable (k : Type) [Field k] (d : ℕ)

/-- The first index of `Fin d`, named once so that every statement below uses
the same term for it. -/
def firstIndex (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

/-! ### `D_d(k)` -/

/-- **The printed `D_d(k)`**: the diagonal matrices of `GL_d(L_k(1,d))` whose
entries are units of `k`. -/
def printedDiagonal : Subgroup (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ :=
  scalarDiagonalGroup (ι := Fin d) (algebraMap k (AryLeavittAlgebra k d))

/-- **`D_d(k)` is abelian.** -/
theorem printedDiagonal_mul_comm
    {A B : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ}
    (hA : A ∈ printedDiagonal k d) (hB : B ∈ printedDiagonal k d) :
    A * B = B * A :=
  scalarDiagonalGroup_mul_comm (algebraMap k (AryLeavittAlgebra k d)) hA hB

/-- **`D_d(k)` normalizes `EL_d(R)`.**  No hypothesis: not `d ≥ 2`, not
countability of `k`. -/
theorem printedDiagonal_le_normalizer :
    printedDiagonal k d ≤ Subgroup.normalizer
      (elementaryGroup (Fin d) (AryLeavittAlgebra k d) :
        Set (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) :=
  scalarDiagonalGroup_le_normalizer (algebraMap k (AryLeavittAlgebra k d))

theorem printedDiagonal_le_diagonalGroup :
    printedDiagonal k d ≤ diagonalGroup (Fin d) (AryLeavittAlgebra k d) :=
  scalarDiagonalGroup_le_diagonalGroup (algebraMap k (AryLeavittAlgebra k d))

/-- A one-coordinate scalar diagonal matrix lies in `D_d(k)`. -/
theorem diagAt_scalarUnits_mem (l : Fin d) (a : kˣ) :
    (diagAt l (LeavittKOneFormula.scalarUnits k d a) :
        (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) ∈
      printedDiagonal k d := by
  show (diagAt l (LeavittKOneFormula.scalarUnits k d a) :
      (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) ∈
    scalarDiagonalGroup (ι := Fin d) (algebraMap k (AryLeavittAlgebra k d))
  refine (mem_scalarDiagonalGroup_iff
      (algebraMap k (AryLeavittAlgebra k d))).mpr
    ⟨fun i ↦ if i = l then a else 1, Units.ext ?_⟩
  rw [diagonalUnit_val, diagAt_val]
  congr 1
  funext i
  by_cases h : i = l <;> simp [h, LeavittKOneFormula.scalarUnits]

/-! ### `GL_d(R) = EL_d(R) · D_d(R^×)`, unconditionally -/

/-- **The decomposition with unrestricted diagonal entries**, for every field
and every `d ≥ 2`: `L_k(1,d)` is purely infinite simple, hence strongly
divisible, so rank-`d` Gaussian elimination applies. -/
theorem exists_elementary_mul_diagonal_ary (hd : 2 ≤ d)
    (A : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) :
    ∃ E ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d),
      ∃ D ∈ diagonalGroup (Fin d) (AryLeavittAlgebra k d), A = E * D := by
  haveI : NeZero d := ⟨by omega⟩
  exact exists_elementary_mul_diagonal (AryLeavitt.hasSingleSandwichDivision k d hd)
    A (firstIndex d hd)

/-- The subgroup form: `EL_d(R) ⊔ D_d(R^×) = GL_d(R)`. -/
theorem elementary_sup_diagonal_ary (hd : 2 ≤ d) :
    elementaryGroup (Fin d) (AryLeavittAlgebra k d) ⊔
        diagonalGroup (Fin d) (AryLeavittAlgebra k d) = ⊤ := by
  haveI : NeZero d := ⟨by omega⟩
  exact elementaryGroup_sup_diagonalGroup_eq_top
    (AryLeavitt.hasSingleSandwichDivision k d hd) (firstIndex d hd)

/-- **`EL_d(R)` is normal in `GL_d(R)`** for `R = L_k(1,d)`, every field and
every `d ≥ 2`.  The printed argument needs this to read `EL_d(R) D_d(k)` as a
subgroup at all. -/
theorem elementaryGroup_normal_ary (hd : 2 ≤ d) :
    (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal := by
  haveI : NeZero d := ⟨by omega⟩
  exact elementaryGroup_normal_of_division
    (AryLeavitt.hasSingleSandwichDivision k d hd) (firstIndex d hd)

/-- **The interface shape, at the generality it can actually carry.**

`o-leavitt-k1` asked for `M = E · diag(c)` with `E` elementary and the entries
`c` scalars from `k^×`.  What is unconditionally true is the same factorisation
with the entries arbitrary units of `R`; the scalar-entry version is
`PrintedKhanhThanhDecomposition` below and is **not** proved here, because it is
equivalent to the open residual.  This statement is the honest one, written in
the requested matrix-entry spelling so the difference is visible: the tuple `c`
lands in `(L_k(1,d))^×`, not in `k^×`. -/
theorem gl_eq_elementary_mul_diagonal (hd : 2 ≤ d)
    (M : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) :
    ∃ E ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d),
      ∃ c : Fin d → (AryLeavittAlgebra k d)ˣ,
        (M : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) =
          (E : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) *
            Matrix.diagonal (fun i ↦ ((c i : AryLeavittAlgebra k d))) := by
  obtain ⟨E, hE, D, hD, rfl⟩ := exists_elementary_mul_diagonal_ary k d hd M
  obtain ⟨c, rfl⟩ := mem_diagonalGroup_iff.mp hD
  exact ⟨E, hE, c, by rw [Units.val_mul, diagonalUnit_val]⟩

/-! ### The printed decomposition and its exact residual -/

/-- **The printed sentence's decomposition**, `GL_d(R) = EL_d(R) D_d(k)`.

The body is deliberately the same matrix-entry statement as
`LeavittKOneScalar.PrintedKhanhThanhDiagonalDecomposition`
(`KOne/LeavittKOneScalarSurjectivity.lean`), which consumes this sentence to
reach `LeavittKOneFormula.ScalarSurjective`.  The two propositions unfold to the
same thing, so a proof of either discharges the other with no bridge lemma.

Note the entries: they are scalars from `k^×`, **not** arbitrary units of `R`.
The version with entries in `R^×` is `exists_elementary_mul_diagonal_ary` above,
it is unconditional, and it is strictly weaker --- it leaves the `K₁`-class of
`M` unconstrained, so it does not reach `ScalarSurjective`. -/
def PrintedKhanhThanhDecomposition : Prop :=
  ∀ M : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ,
    ∃ E ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d), ∃ c : Fin d → kˣ,
      (M : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) =
        (E : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) *
          Matrix.diagonal
            (fun i ↦ algebraMap k (AryLeavittAlgebra k d) ((c i : k)))

/-- **The residual**: every diagonal matrix over `R^×` is an elementary matrix
times a *scalar* diagonal one.  This is the unstable form of
`LeavittKOneFormula.ScalarSurjective`. -/
def UnstableScalarSurjective : Prop :=
  ∀ D ∈ diagonalGroup (Fin d) (AryLeavittAlgebra k d),
    ∃ E ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d),
      ∃ C ∈ printedDiagonal k d, D = E * C

/-- Membership in `D_d(k)`, read off as an entrywise formula. -/
theorem exists_scalar_entries_of_mem
    {C : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ}
    (hC : C ∈ printedDiagonal k d) :
    ∃ c : Fin d → kˣ,
      (C : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) =
        Matrix.diagonal
          (fun i ↦ algebraMap k (AryLeavittAlgebra k d) ((c i : k))) := by
  obtain ⟨c, hc⟩ := (mem_scalarDiagonalGroup_iff
    (algebraMap k (AryLeavittAlgebra k d))).mp hC
  refine ⟨c, ?_⟩
  subst hc
  rfl

/-- The converse reading: a tuple of scalars names an element of `D_d(k)`. -/
theorem exists_mem_printedDiagonal (c : Fin d → kˣ) :
    ∃ C ∈ printedDiagonal k d,
      (C : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) =
        Matrix.diagonal
          (fun i ↦ algebraMap k (AryLeavittAlgebra k d) ((c i : k))) :=
  ⟨diagonalUnit (fun i ↦ Units.map
      ((algebraMap k (AryLeavittAlgebra k d)) : k →* AryLeavittAlgebra k d)
      (c i)),
    scalarDiagonalUnit_mem (algebraMap k (AryLeavittAlgebra k d)) c, rfl⟩

/-- **The printed decomposition is equivalent to the residual**, at every
`d ≥ 2`: nothing is lost by attacking `UnstableScalarSurjective`, and nothing
weaker than it suffices. -/
theorem printedKhanhThanhDecomposition_iff (hd : 2 ≤ d) :
    PrintedKhanhThanhDecomposition k d ↔ UnstableScalarSurjective k d := by
  constructor
  · intro h D _
    obtain ⟨E, hE, c, hval⟩ := h D
    obtain ⟨C, hCmem, hCval⟩ := exists_mem_printedDiagonal k d c
    exact ⟨E, hE, C, hCmem, Units.ext (by rw [Units.val_mul, hCval, hval])⟩
  · intro h M
    obtain ⟨E, hE, D, hD, rfl⟩ := exists_elementary_mul_diagonal_ary k d hd M
    obtain ⟨E', hE', C, hC, rfl⟩ := h D hD
    obtain ⟨c, hCval⟩ := exists_scalar_entries_of_mem k d hC
    refine ⟨E * E', mul_mem hE hE', c, ?_⟩
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hCval, mul_assoc]

/-- **The printed decomposition from a statement about a single unit.**

If every unit `u` of `R` agrees, modulo `EL_d(R)`, with a scalar in the first
diagonal slot, then `GL_d(R) = EL_d(R) D_d(k)`.  The hypothesis is the unstable
form of `LeavittKOneFormula.ScalarSurjective k d`, which that file records as
open for `d ≥ 3` and which is the same content as the `K₁` half of the
Khanh--Thanh citation. -/
theorem printedKhanhThanhDecomposition_of_diagAt (hd : 2 ≤ d)
    (h : ∀ u : (AryLeavittAlgebra k d)ˣ, ∃ a : kˣ,
      (diagAt (firstIndex d hd) u :
          (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) *
        (diagAt (firstIndex d hd)
          (LeavittKOneFormula.scalarUnits k d a))⁻¹ ∈
        elementaryGroup (Fin d) (AryLeavittAlgebra k d)) :
    PrintedKhanhThanhDecomposition k d := by
  haveI : NeZero d := ⟨by omega⟩
  refine (printedKhanhThanhDecomposition_iff k d hd).mpr ?_
  intro D _
  obtain ⟨E, hE, F, hF, u, hA⟩ :=
    eq_elementary_mul_diagAt (AryLeavitt.hasSingleSandwichDivision k d hd) D
      (firstIndex d hd)
  obtain ⟨a, hX⟩ := h u
  have hCmem : (diagAt (firstIndex d hd)
      (LeavittKOneFormula.scalarUnits k d a) :
        (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) ∈
      printedDiagonal k d := diagAt_scalarUnits_mem k d _ a
  have hconj : (diagAt (firstIndex d hd)
        (LeavittKOneFormula.scalarUnits k d a) :
          (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) * F *
      (diagAt (firstIndex d hd)
        (LeavittKOneFormula.scalarUnits k d a) :
          (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ)⁻¹ ∈
      elementaryGroup (Fin d) (AryLeavittAlgebra k d) :=
    conj_mem_of_mem_diagonalGroup
      (printedDiagonal_le_diagonalGroup k d hCmem) hF
  refine ⟨E * ((diagAt (firstIndex d hd) u :
        (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) *
      (diagAt (firstIndex d hd)
        (LeavittKOneFormula.scalarUnits k d a))⁻¹) *
      ((diagAt (firstIndex d hd)
          (LeavittKOneFormula.scalarUnits k d a) :
            (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) * F *
        (diagAt (firstIndex d hd)
          (LeavittKOneFormula.scalarUnits k d a))⁻¹),
    mul_mem (mul_mem hE hX) hconj, _, hCmem, ?_⟩
  rw [hA]
  group

end KhanhThanhDiagonal
end OneSidedMFRadical
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

open GroupApproximation.Manuscript.OneSidedMFRadical in
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedDiagonal_mul_comm

open GroupApproximation.Manuscript.OneSidedMFRadical in
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedDiagonal_le_normalizer

open GroupApproximation.Manuscript.OneSidedMFRadical in
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.exists_elementary_mul_diagonal_ary

open GroupApproximation.Manuscript.OneSidedMFRadical in
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.elementaryGroup_normal_ary

open GroupApproximation.Manuscript.OneSidedMFRadical in
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.gl_eq_elementary_mul_diagonal

open GroupApproximation.Manuscript.OneSidedMFRadical in
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.elementary_sup_diagonal_ary

open GroupApproximation.Manuscript.OneSidedMFRadical in
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedKhanhThanhDecomposition_iff

open GroupApproximation.Manuscript.OneSidedMFRadical in
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedKhanhThanhDecomposition_of_diagAt
