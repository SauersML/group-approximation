import GroupApproximation.Analysis.AmenableQuasidiagonal
import GroupApproximation.Algebra.AmenableLocallyFiniteByInt
import GroupApproximation.Sofic.AmenableActionSofic
import GroupApproximation.Sofic.CliffordBSAmenable
import GroupApproximation.Monsters.CyclicBaseLEFObstruction

/-!
# The Følner route to MF certifies exactly the LEF groups

`non_mf_group_notes.tex`, `\section{The cyclic comparison}`
`\label{sec:necessity}`, paragraph *Sharpness of the Kazhdan hypothesis*
(grep `"hence MF by"`, not a line number --- the file is edited
concurrently): the realized Clifford quotient of Theorem C "is a subgroup of
this amenable group and is therefore amenable, hence MF by \cite{TWW}".  The
same implication is used again in `\label{sec:consequences}` (grep
`"homomorphism to any countable"`), there for *arbitrary* countable amenable
groups rather than for this one.

`Sofic.CliffordBSAmenable` machine-checks every step of that sentence except
the last one.  This file settles what the last one costs.

## The question this file answers

An amenable group has Følner sets, and completing each translation of a Følner
set to a permutation of it gives finite-dimensional almost representations by
permutation matrices --- the repository builds them in
`AmenableActionSofic.folnerPerm`.  That is the elementary route one would hope
to use in place of Tikuisis--White--Winter.  It works for soficity, whose
metric is normalized Hamming distance.  Does it work for MF, whose metric is
the operator norm?

It does not, and the failure is total rather than quantitative.
`Analysis.AmenableQuasidiagonal` proves that the operator-norm
multiplicativity defect of a permutation model is either `0` or at least `1`.
Here that dichotomy is turned into a group-theoretic statement:

* `isLEF_of_hasPermutationNormModels`: a group with permutation
  operator-norm models of defect below `1` on every finite set is LEF;
* `hasPermutationNormModels_of_isLEF`: conversely, every LEF group has such
  models, with defect exactly `0`;
* `isLEF_iff_hasPermutationNormModels`: so the permutation route detects
  **exactly** the LEF groups, and nothing beyond them.

The dichotomy is also recorded directly on the repository's Følner
permutations (`folnerPerm_l2_opNorm_defect_eq_zero_or_one_le`).

Applied to the manuscript's own object, and using the repository's proof that
the realized Clifford quotient is not LEF
(`CyclicBaseLEFObstruction.realizedQuotient_not_isLEF`, which the manuscript
already cites by `\leanverified` two paragraphs after the sentence above):

* `realizedQuotient_isAmenable_and_not_hasPermutationNormModels`: the realized
  Clifford quotient is amenable and admits **no** permutation operator-norm
  model at any accuracy.

## What remains unproved, and why it is stated rather than hidden

The manuscript's "hence MF" is Tikuisis--White--Winter.  It is not proved
here, it is not provable from anything in this repository, and no hypothesis
in this file stands in for it.  The positive MF results the repository does
have --- `isOperatorMF_of_residuallyFinite`, `isOperatorMF_of_isLEF`,
`isOperatorMF_of_locallyFinite` --- all factor through *exact* finite models,
and the theorems below show that the Følner construction cannot escape that
class.  Certifying the manuscript's sentence therefore requires genuinely
non-permutation unitaries, which is precisely the quasidiagonality input.

`isAmenable_and_isOperatorMF_of_isLocallyFiniteGroup` records the reachable
case: for locally finite groups both halves --- amenability and MF --- are
machine-checked, because such groups are LEF.  The same holds for residually
finite amenable groups.  No amenable group outside the LEF class is certified
MF anywhere in this repository, and by the theorems above the Følner
construction cannot change that.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-! ## Permutation operator-norm models -/

/-- A group **has permutation operator-norm models** when every finite test
set carries a finite model, an assignment of permutations to group elements
that is injective on the test set, and an operator-norm multiplicativity
defect strictly below `1` on the test set.

This is the shape of every model the Følner construction produces: the
unitaries are permutation matrices, separation is injectivity of the
underlying permutations, and multiplicativity is measured in operator norm as
the MF property requires. -/
def HasPermutationNormModels (G : Type u) [Group G] : Prop :=
  ∀ s : Finset G, ∃ (Y : FiniteModel) (u : G → Equiv.Perm Y),
    Set.InjOn u (s : Set G) ∧
      ∀ x ∈ s, ∀ y ∈ s,
        ‖(u x).permMatrix ℂ * (u y).permMatrix ℂ -
          (u (x * y)).permMatrix ℂ‖ < 1

omit [Group G] in
/-- **The separation clause above is the honest one.**  For permutation
models, operator-norm separation of the matrices is *equivalent* to
injectivity of the underlying permutations: distinct permutations are
automatically `1`-separated, and equal ones are not separated at all.  So
demanding `Set.InjOn` is neither weaker nor stronger than demanding a corona
separation constant. -/
theorem injOn_iff_l2_opNorm_separated (Y : FiniteModel) (u : G → Equiv.Perm Y)
    (s : Finset G) :
    Set.InjOn u (s : Set G) ↔
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        1 ≤ ‖(u x).permMatrix ℂ - (u y).permMatrix ℂ‖ := by
  constructor
  · intro hinj x hx y hy hne
    refine one_le_l2_opNorm_permMatrix_sub Y ?_
    intro hcontra
    exact hne (hinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hcontra)
  · intro hsep x hx y hy hxy
    by_contra hne
    have hbound := hsep x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hne
    rw [hxy, sub_self, norm_zero] at hbound
    linarith

/-! ## The route certifies exactly LEF -/

/-- **Step 1: below the threshold, approximate means exact.**  A permutation
model of defect below `1` is an exact anti-homomorphism on its test set. -/
theorem perm_mul_eq_of_permutationNormModel
    {Y : FiniteModel} {u : G → Equiv.Perm Y} {s : Finset G}
    (hmul : ∀ x ∈ s, ∀ y ∈ s,
      ‖(u x).permMatrix ℂ * (u y).permMatrix ℂ -
        (u (x * y)).permMatrix ℂ‖ < 1)
    {x y : G} (hx : x ∈ s) (hy : y ∈ s) : u y * u x = u (x * y) :=
  perm_mul_eq_of_l2_opNorm_defect_lt_one Y (hmul x hx y hy)

/-- **Step 2: an exact anti-homomorphism into a finite permutation group is a
local embedding.**  Inverting turns the anti-homomorphism into a homomorphism,
and the finite target is the permutation group of the model.

Hence a group with permutation operator-norm models is LEF: the operator-norm
threshold leaves no room for genuine approximation. -/
theorem isLEF_of_hasPermutationNormModels (h : HasPermutationNormModels G) :
    IsLEF G := by
  rw [isLEF_iff_textbook]
  intro s
  obtain ⟨Y, u, hinj, hmul⟩ := h s
  refine ⟨{ groupCarrier := Equiv.Perm Y
            group := inferInstance
            fintype := inferInstance
            decidableEq := inferInstance },
          fun g ↦ (u g)⁻¹, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj hx hy (inv_injective hxy)
  · intro x hx y hy _
    have hstep : u y * u x = u (x * y) :=
      perm_mul_eq_of_permutationNormModel hmul hx hy
    have hgoal : (u (x * y))⁻¹ = (u x)⁻¹ * (u y)⁻¹ := by
      rw [← hstep, _root_.mul_inv_rev]
    exact hgoal

/-- **The converse.**  Every LEF group has permutation operator-norm models,
and their defect is not merely below `1` but exactly `0`. -/
theorem hasPermutationNormModels_of_isLEF (h : IsLEF G) :
    HasPermutationNormModels G := by
  intro s
  obtain ⟨n, f, hinj, hlm⟩ := h s
  refine ⟨⟨Fin n, inferInstance, inferInstance⟩, fun g ↦ (f g)⁻¹, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj hx hy (inv_injective hxy)
  · intro x hx y hy
    have hperm : ((f y)⁻¹ * (f x)⁻¹ : Equiv.Perm (Fin n)) = (f (x * y))⁻¹ := by
      rw [hlm.map_mul x hx y hy, _root_.mul_inv_rev]
    have hmat :
        ((f x)⁻¹ : Equiv.Perm (Fin n)).permMatrix ℂ *
              ((f y)⁻¹ : Equiv.Perm (Fin n)).permMatrix ℂ
            - ((f (x * y))⁻¹ : Equiv.Perm (Fin n)).permMatrix ℂ = 0 := by
      rw [← Matrix.permMatrix_mul, hperm, sub_self]
    have hnorm :
        ‖((f x)⁻¹ : Equiv.Perm (Fin n)).permMatrix ℂ *
              ((f y)⁻¹ : Equiv.Perm (Fin n)).permMatrix ℂ
            - ((f (x * y))⁻¹ : Equiv.Perm (Fin n)).permMatrix ℂ‖ < 1 := by
      rw [hmat, norm_zero]
      exact zero_lt_one
    exact hnorm

/-- **The permutation route detects exactly the LEF groups.**  Operator-norm
approximation by permutation matrices is not a weaker demand than exact local
embedding into finite groups; it is the same demand. -/
theorem isLEF_iff_hasPermutationNormModels :
    IsLEF G ↔ HasPermutationNormModels G :=
  ⟨hasPermutationNormModels_of_isLEF, isLEF_of_hasPermutationNormModels⟩

/-- The route does deliver MF where it applies --- but only through
`isOperatorMF_of_isLEF`, that is, only for LEF groups. -/
theorem isOperatorMF_of_hasPermutationNormModels [Countable G]
    (h : HasPermutationNormModels G) : IsOperatorMF G :=
  isOperatorMF_of_isLEF (isLEF_of_hasPermutationNormModels h)

/-- **The no-go, contrapositive form.**  A group that is not LEF has no
permutation operator-norm model at any accuracy, no matter how large the
Følner set or how small its boundary. -/
theorem not_hasPermutationNormModels_of_not_isLEF (h : ¬ IsLEF G) :
    ¬ HasPermutationNormModels G :=
  fun hp ↦ h (isLEF_of_hasPermutationNormModels hp)

/-! ## The repository's own Følner permutations

`AmenableActionSofic.folnerPerm A q` completes left translation by `q`,
restricted to a Følner set `A`, to a permutation of `A`.  Those are exactly
the matrices the Følner route would feed to an MF model, so the dichotomy is
recorded directly on them rather than only on the abstract shape above. -/

/-- A Følner set, packaged as a finite model. -/
abbrev folnerModel {Q : Type} [Group Q] [DecidableEq Q] (A : Finset Q) :
    FiniteModel :=
  ⟨↥A, inferInstance, inferInstance⟩

/-- **The Følner model's operator-norm multiplicativity defect is `0` or at
least `1`.**  Enlarging the Følner set drives the normalized Hamming defect to
zero --- that is `AmenableActionSofic.exists_folner` --- and leaves this
quantity exactly where it was. -/
theorem folnerPerm_l2_opNorm_defect_eq_zero_or_one_le
    {Q : Type} [Group Q] [DecidableEq Q] (A : Finset Q) (q₁ q₂ : Q) :
    ‖(AmenableActionSofic.folnerPerm A q₁).permMatrix ℂ *
            (AmenableActionSofic.folnerPerm A q₂).permMatrix ℂ
          - (AmenableActionSofic.folnerPerm A (q₁ * q₂)).permMatrix ℂ‖ = 0 ∨
      1 ≤ ‖(AmenableActionSofic.folnerPerm A q₁).permMatrix ℂ *
            (AmenableActionSofic.folnerPerm A q₂).permMatrix ℂ
          - (AmenableActionSofic.folnerPerm A (q₁ * q₂)).permMatrix ℂ‖ :=
  l2_opNorm_permMatrix_defect_eq_zero_or_one_le (folnerModel A) _ _ _

/-- **What "small operator-norm defect" costs a Følner model.**  It forces the
completed translations to compose *exactly*, as permutations of the whole
Følner set --- including its boundary, which is precisely where the completion
`Localization.exists_completion` is arbitrary and where almost-invariance
gives no information.  Følner sets control the size of that boundary; they
never remove it. -/
theorem folnerPerm_mul_eq_of_l2_opNorm_defect_lt_one
    {Q : Type} [Group Q] [DecidableEq Q] (A : Finset Q) (q₁ q₂ : Q)
    (h : ‖(AmenableActionSofic.folnerPerm A q₁).permMatrix ℂ *
            (AmenableActionSofic.folnerPerm A q₂).permMatrix ℂ
          - (AmenableActionSofic.folnerPerm A (q₁ * q₂)).permMatrix ℂ‖ < 1) :
    AmenableActionSofic.folnerPerm A q₂ * AmenableActionSofic.folnerPerm A q₁
      = AmenableActionSofic.folnerPerm A (q₁ * q₂) :=
  perm_mul_eq_of_l2_opNorm_defect_lt_one (folnerModel A) h

/-! ## The reachable positive class

Locally finite groups are amenable and MF, both halves proved.  The
certification runs through exact finite models, as does every other positive
MF result in this repository. -/

/-- **Amenable and MF, with both halves machine-checked**, for countable
locally finite groups. -/
theorem isAmenable_and_isOperatorMF_of_isLocallyFiniteGroup
    {K : Type} [Group K] [Countable K] (h : IsLocallyFiniteGroup K) :
    Amenability.IsAmenable K ∧ IsOperatorMF K :=
  ⟨Amenability.isAmenable_of_hasInvariantMean
      (Amenability.hasInvariantMean_of_isLocallyFiniteGroup h),
    isOperatorMF_of_locallyFinite h⟩

/-! ## The manuscript's own group

The sharpness paragraph applies "amenable, hence MF" to the realized Clifford
quotient of Theorem C.  That group is amenable
(`CyclicBaseCalibration.isAmenable_subgroup_CliffordBS`) and not LEF
(`CyclicBaseLEFObstruction.realizedQuotient_not_isLEF`).  The two facts
together locate the manuscript's citation exactly. -/

/-- **The manuscript's group is amenable and has no permutation operator-norm
model.**

So the corona representation that the sharpness paragraph needs cannot be
assembled from Følner sets: its unitaries must fail to be permutation
matrices.  This is exactly the content of the citation to
Tikuisis--White--Winter, isolated as a theorem rather than left as prose, and
nothing in this repository supplies it. -/
theorem realizedQuotient_isAmenable_and_not_hasPermutationNormModels :
    Amenability.IsAmenable LiteralCyclicCalibration.RealizedQuotient ∧
      ¬ HasPermutationNormModels LiteralCyclicCalibration.RealizedQuotient :=
  ⟨CyclicBaseCalibration.isAmenable_subgroup_CliffordBS
      LiteralCyclicCalibration.realization.range,
    not_hasPermutationNormModels_of_not_isLEF
      CyclicBaseLEFObstruction.realizedQuotient_not_isLEF⟩

end GroupApproximation
