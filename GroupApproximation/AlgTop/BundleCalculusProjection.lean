import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

/-!
# Bundle calculus I: projections up to unitary conjugation

A complex vector bundle over a compact Hausdorff space is, in this development, a
projection in a matrix algebra over the space, and two bundles are isomorphic when
the two projections are Murray-von Neumann equivalent.  Everything the
characteristic-class lanes need about that dictionary rests on one theorem, and
this file proves it:

> a *continuous family of projections indexed by a preconnected space* is
> constant up to unitary conjugation.

Homotopy invariance is the case where the index space is `[0,1]`.  Nothing here
mentions bundles, matrices or compactness: the statement lives in an arbitrary
unital C*-algebra, so the matrix model, the corner algebras and the pullback
constructions all inherit it for free.

## The proof

The local step is the classical estimate that projections at distance `< 1` are
unitarily conjugate.  Given projections `p`, `q` with `‖p - q‖ < 1`, put

    z = q p + (1 - q)(1 - p).

Then `z p = q z = q p`, so `z` intertwines `p` and `q`, and a two-line expansion
using only `p² = p`, `q² = q` gives

    z* z = z z* = 1 - (p - q)²  =: a.

So `z` is normal, `a` is positive, and `‖1 - a‖ ≤ ‖p - q‖² < 1` makes `a`
invertible.  The polar part `u = z a^(-1/2)` is then a unitary, because
`a^(-1/2)` commutes with everything `a` commutes with -- it is a continuous
function of `a` -- and `a` commutes with `p` (the square `(p - q)²` does) and
with `z` (normality).  The same commutation turns `z p = q z` into `u p = q u`,
which is `u p u* = q`.

The global step is a connectedness argument rather than a subdivision: the set of
indices whose projection is unitarily conjugate to a fixed one is *open*, by the
local step, and so is its complement, by the local step again together with
symmetry of conjugacy.  A nonempty clopen subset of a preconnected space is
everything.

## Manuscript status

Machinery.  This is the substrate the Chern-class, K-theory and Euler-class lanes
stand on; it certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace BundleCalculus

open scoped NNReal

section Defs

variable {R : Type*}

/-- Unitary conjugacy: `q = u p u*` for a unitary `u`.  Stronger than
`MurrayVonNeumannEquiv` in general, and what the analytic arguments actually
produce. -/
def UnitaryConj [Monoid R] [StarMul R] (p q : R) : Prop :=
  ∃ u ∈ unitary R, u * p * star u = q

end Defs

namespace UnitaryConj

variable {R : Type*} [Monoid R] [StarMul R] {p q r : R}

@[refl]
theorem refl (p : R) : UnitaryConj p p :=
  ⟨1, one_mem _, by simp⟩

theorem symm (h : UnitaryConj p q) : UnitaryConj q p := by
  obtain ⟨u, hu, huq⟩ := h
  refine ⟨star u, Unitary.star_mem hu, ?_⟩
  have h1 : star u * u = 1 := Unitary.star_mul_self_of_mem hu
  rw [← huq, star_star]
  simp only [mul_assoc]
  rw [h1, mul_one, ← mul_assoc, h1, one_mul]

theorem trans (h₁ : UnitaryConj p q) (h₂ : UnitaryConj q r) : UnitaryConj p r := by
  obtain ⟨u, hu, hup⟩ := h₁
  obtain ⟨v, hv, hvq⟩ := h₂
  refine ⟨v * u, mul_mem hv hu, ?_⟩
  rw [← hvq, ← hup, star_mul]
  simp only [mul_assoc]

end UnitaryConj

section Ring

variable {R : Type*} [Ring R] [StarRing R] {p q : R}

/-- Unitary conjugacy of a projection with anything is Murray-von Neumann
equivalence -- so bundle isomorphism, in the projection model.  The repo's
`MurrayVonNeumannEquiv.of_isometry_conjugate` already does the work: it needs
only `star u * u = 1`, so unitarity is more than required.  This is that lemma
phrased against `UnitaryConj`, which is what the analytic theorems below
produce. -/
theorem UnitaryConj.murrayVonNeumannEquiv (hp : IsStarProjection p) (h : UnitaryConj p q) :
    MurrayVonNeumannEquiv p q := by
  obtain ⟨u, hu, huq⟩ := h
  rw [← huq]
  exact MurrayVonNeumannEquiv.of_isometry_conjugate hp (Unitary.star_mul_self_of_mem hu)

end Ring

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Close projections are unitarily conjugate.**  If `‖p - q‖ < 1` then
`q = u p u*` for an explicit unitary `u`, namely the polar part of
`q p + (1 - q)(1 - p)`.

This is the whole analytic content of homotopy invariance in the projection
model, and the constant `1` is what makes the connectedness argument in
`unitaryConj_of_preconnected` go through with no quantitative bookkeeping. -/
theorem unitaryConj_of_norm_sub_lt_one {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    UnitaryConj p q := by
  have hp2 : p * p = p := hp.isIdempotentElem
  have hq2 : q * q = q := hq.isIdempotentElem
  have hps : star p = p := hp.isSelfAdjoint.star_eq
  have hqs : star q = q := hq.isSelfAdjoint.star_eq
  have hpp : ∀ x : A, p * (p * x) = p * x := fun x => by rw [← mul_assoc, hp2]
  have hqq : ∀ x : A, q * (q * x) = q * x := fun x => by rw [← mul_assoc, hq2]
  obtain ⟨z, hzdef⟩ : ∃ z : A, z = q * p + (1 - q) * (1 - p) := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : A, a = 1 - (p - q) * (p - q) := ⟨_, rfl⟩
  have hzs : star z = p * q + (1 - p) * (1 - q) := by
    rw [hzdef]
    simp only [star_add, star_mul, star_sub, star_one, hps, hqs]
  -- The four algebraic identities.  Each is a distribution followed by the two
  -- idempotent relations; nothing else about `p` and `q` is used.
  have hzz : star z * z = a := by
    rw [hzs, hzdef, hadef]
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, mul_assoc,
      hpp, hqq, hp2, hq2]
    try abel
  have hzz' : z * star z = a := by
    rw [hzs, hzdef, hadef]
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, mul_assoc,
      hpp, hqq, hp2, hq2]
    try abel
  have hzp : z * p = q * z := by
    rw [hzdef]
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, mul_assoc,
      hpp, hqq, hp2, hq2]
    try abel
  have hap : Commute a p := by
    refine (commute_iff_eq _ _).mpr ?_
    rw [hadef]
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, mul_assoc,
      hpp, hqq, hp2, hq2]
    try abel
  -- `z` is normal, so `a` commutes with `z` and with `z*`.
  have haz : Commute a z := by
    refine (commute_iff_eq _ _).mpr ?_
    calc a * z = z * star z * z := by rw [hzz']
      _ = z * (star z * z) := mul_assoc _ _ _
      _ = z * a := by rw [hzz]
  have hastar : star a = a := by
    conv_lhs => rw [← hzz]
    rw [star_mul, star_star, hzz]
  have hazs : Commute a (star z) := by
    refine (commute_iff_eq _ _).mpr ?_
    have hst := congrArg star haz.eq
    rw [star_mul, star_mul, hastar] at hst
    exact hst.symm
  -- `a` is a positive unit, so it has an inverse square root.
  have hnorm : ‖(p - q) * (p - q)‖ < 1 := by
    have h0 : (0 : ℝ) ≤ ‖p - q‖ := norm_nonneg _
    calc ‖(p - q) * (p - q)‖ ≤ ‖p - q‖ * ‖p - q‖ := norm_mul_le _ _
      _ < 1 := by nlinarith
  have haunit : IsUnit a := by
    rw [hadef]; exact isUnit_one_sub_of_norm_lt_one hnorm
  have hanonneg : (0 : A) ≤ a := by rw [← hzz]; exact star_mul_self_nonneg z
  have hasp : IsStrictlyPositive a := haunit.isStrictlyPositive hanonneg
  obtain ⟨b, hbdef⟩ : ∃ b : A, b = a ^ (-(2⁻¹) : ℝ) := ⟨_, rfl⟩
  have hbnonneg : (0 : A) ≤ b := by rw [hbdef]; exact CFC.rpow_nonneg
  have hbs : star b = b := hbnonneg.star_eq
  have hexp : (-(2⁻¹) : ℝ) + (-(2⁻¹) : ℝ) = -(1 : ℝ) := by norm_num
  have hbb : b * b = a ^ (-(1 : ℝ)) := by
    rw [hbdef, ← CFC.rpow_add haunit, hexp]
  have hab : a * (b * b) = 1 := by
    have hx := CFC.rpow_mul_rpow_neg (a := a) 1 hasp
    rw [CFC.rpow_one a hanonneg] at hx
    rw [hbb]; exact hx
  have hba : b * b * a = 1 := by
    have hx := CFC.rpow_neg_mul_rpow (a := a) 1 hasp
    rw [CFC.rpow_one a hanonneg] at hx
    rw [hbb]; exact hx
  -- `b` is a continuous function of `a`, so it inherits every commutation of `a`.
  have hcab : Commute a b := by
    rw [hbdef, CFC.rpow_def]
    exact (Commute.cfc_nnreal (Commute.refl a) _).symm
  have hbp : Commute b p := by
    rw [hbdef, CFC.rpow_def]
    exact Commute.cfc_nnreal hap _
  have hbzs : Commute b (star z) := by
    rw [hbdef, CFC.rpow_def]
    exact Commute.cfc_nnreal hazs _
  -- the polar part
  obtain ⟨u, hudef⟩ : ∃ u : A, u = z * b := ⟨_, rfl⟩
  have hus : star u = b * star z := by rw [hudef, star_mul, hbs]
  have h1 : star u * u = 1 := by
    rw [hus, hudef]
    calc b * star z * (z * b) = b * (star z * z * b) := by simp only [mul_assoc]
      _ = b * (a * b) := by rw [hzz]
      _ = b * (b * a) := by rw [hcab.eq]
      _ = b * b * a := (mul_assoc b b a).symm
      _ = 1 := hba
  have h2 : u * star u = 1 := by
    rw [hus, hudef]
    calc z * b * (b * star z) = z * (b * b * star z) := by simp only [mul_assoc]
      _ = z * (star z * (b * b)) := by rw [(hbzs.mul_left hbzs).eq]
      _ = z * star z * (b * b) := (mul_assoc z (star z) (b * b)).symm
      _ = a * (b * b) := by rw [hzz']
      _ = 1 := hab
  have h3 : u * p = q * u := by
    rw [hudef]
    calc z * b * p = z * (p * b) := by rw [mul_assoc, hbp.eq]
      _ = z * p * b := (mul_assoc z p b).symm
      _ = q * z * b := by rw [hzp]
      _ = q * (z * b) := mul_assoc _ _ _
  refine ⟨u, Unitary.mem_iff.mpr ⟨h1, h2⟩, ?_⟩
  calc u * p * star u = q * u * star u := by rw [h3]
    _ = q * (u * star u) := mul_assoc _ _ _
    _ = q := by rw [h2, mul_one]

/-- Murray-von Neumann form of `unitaryConj_of_norm_sub_lt_one`. -/
theorem murrayVonNeumannEquiv_of_norm_sub_lt_one {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    MurrayVonNeumannEquiv p q :=
  (unitaryConj_of_norm_sub_lt_one hp hq h).murrayVonNeumannEquiv hp

/-- **Homotopy invariance, abstract form.**  A continuous family of projections
indexed by a preconnected space is constant up to unitary conjugation.

The proof is that `{y | UnitaryConj (f y₀) (f y)}` is clopen: both it and its
complement are unions of the balls on which `unitaryConj_of_norm_sub_lt_one`
applies. -/
theorem unitaryConj_of_preconnected {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y]
    {f : Y → A} (hf : Continuous f) (hproj : ∀ y, IsStarProjection (f y)) (y₀ y₁ : Y) :
    UnitaryConj (f y₀) (f y₁) := by
  have hball : ∀ y : Y, IsOpen {z : Y | ‖f z - f y‖ < 1} := fun y =>
    isOpen_lt ((hf.sub continuous_const).norm) continuous_const
  have hself : ∀ y : Y, y ∈ {z : Y | ‖f z - f y‖ < 1} := by
    intro y; simp
  have hnear : ∀ y z : Y, ‖f z - f y‖ < 1 → UnitaryConj (f y) (f z) := by
    intro y z hz
    refine unitaryConj_of_norm_sub_lt_one (hproj y) (hproj z) ?_
    rw [norm_sub_rev]
    exact hz
  have hopen : IsOpen {y : Y | UnitaryConj (f y₀) (f y)} := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    rw [Set.mem_setOf_eq] at hy
    refine ⟨{z : Y | ‖f z - f y‖ < 1}, ?_, hball y, hself y⟩
    intro z hz
    rw [Set.mem_setOf_eq] at hz
    rw [Set.mem_setOf_eq]
    exact hy.trans (hnear y z hz)
  have hcompl : IsOpen {y : Y | UnitaryConj (f y₀) (f y)}ᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hy
    refine ⟨{z : Y | ‖f z - f y‖ < 1}, ?_, hball y, hself y⟩
    intro z hz
    rw [Set.mem_setOf_eq] at hz
    rw [Set.mem_compl_iff, Set.mem_setOf_eq]
    intro hzS
    exact hy (hzS.trans (hnear y z hz).symm)
  have hne : ({y : Y | UnitaryConj (f y₀) (f y)}).Nonempty := by
    refine ⟨y₀, ?_⟩
    rw [Set.mem_setOf_eq]
    exact UnitaryConj.refl _
  have huniv : {y : Y | UnitaryConj (f y₀) (f y)} = Set.univ :=
    IsClopen.eq_univ ⟨⟨hcompl⟩, hopen⟩ hne
  have hmem : y₁ ∈ {y : Y | UnitaryConj (f y₀) (f y)} := by
    rw [huniv]; exact Set.mem_univ y₁
  rw [Set.mem_setOf_eq] at hmem
  exact hmem

/-- The same statement for a preconnected *subset* of the index space, which is
the form the interval `[0,1]` arrives in. -/
theorem unitaryConj_of_isPreconnected {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (hs : IsPreconnected s) {f : Y → A} (hf : Continuous f)
    (hproj : ∀ y, IsStarProjection (f y)) {y₀ y₁ : Y} (h₀ : y₀ ∈ s) (h₁ : y₁ ∈ s) :
    UnitaryConj (f y₀) (f y₁) := by
  haveI : PreconnectedSpace s := Subtype.preconnectedSpace hs
  exact unitaryConj_of_preconnected (f := fun y : s => f (y : Y))
    (hf.comp continuous_subtype_val) (fun y => hproj _) ⟨y₀, h₀⟩ ⟨y₁, h₁⟩

/-- **Homotopy invariance over `[0,1]`.**  A continuous path of projections has
unitarily conjugate -- so Murray-von Neumann equivalent -- endpoints. -/
theorem unitaryConj_of_path {f : ℝ → A} (hf : Continuous f)
    (hproj : ∀ t : ℝ, IsStarProjection (f t)) :
    UnitaryConj (f 0) (f 1) :=
  unitaryConj_of_isPreconnected (s := Set.Icc (0 : ℝ) 1) isPreconnected_Icc hf hproj
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)

/-- Murray-von Neumann form of `unitaryConj_of_path`. -/
theorem murrayVonNeumannEquiv_of_path {f : ℝ → A} (hf : Continuous f)
    (hproj : ∀ t : ℝ, IsStarProjection (f t)) :
    MurrayVonNeumannEquiv (f 0) (f 1) :=
  (unitaryConj_of_path hf hproj).murrayVonNeumannEquiv (hproj 0)

end CStar

end BundleCalculus
end GroupApproximation
