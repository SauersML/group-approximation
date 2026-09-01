import GroupApproximation.GGT.KazhdanHypGirthEight
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.Data.ZMod.Basic

/-!
# Proper-power relators and torsion in girth-eight triangle presentations

Huebschmann, *Cohomology theory of aspherical groups and of small cancellation
groups*, Journal of Pure and Applied Algebra 14 (1979), Theorems 3 and 4,
proves two facts used here.  A `C(6)`, `C(4)`--`T(4)`, or `C(3)`--`T(6)`
presentation is aspherical; and if an element of order `1 < s < infinity`
lies in a group with an aspherical presentation, then some relator has the
form `z ^ q`, with `s` dividing `q`, and the element is conjugate to
`z ^ (q / s)`.  The statements are reproduced before Theorem A in Karol
Duda, *Torsion subgroups of small cancellation groups*, arXiv:2112.01912,
section `Proof of Theorem A` (`all3.tex`, lines 1234--1249 in the fetched
source).

This file proves the algebraic part needed for a positive triangular
presentation:

* `positive_triangle_cube_of_relatorIsProperPower` proves, in the free group,
  that a positive relator of literal length three can be a proper power only
  when its three signed letters are equal.  The proof uses exponent-sum maps,
  so the hypothesis is an equality of free-group elements rather than an
  equality of unreduced lists.
* `GirthEightChecks.relators_not_properPower` combines that theorem with
  `GirthEightChecks.noCube`.
* `FiniteOrderForcesRelatorProperPower` is the exact consequence of
  Huebschmann's localization theorem consumed by torsion-freeness.
  `presented_isPowerTorsionFree_of_finiteOrderForcesRelatorProperPower`
  proves the remaining implication.
* `girthEightTorsionFree_of_localization` reduces
  `GirthEightTorsionFree` to the one geometric localization statement.

The current `GGT/VanKampen/DiscDiagram.lean` defines reduced planar disc
diagrams, but it has no spherical or annular diagrams.  Thus the missing
localization theorem is kept separate from the disc-curvature interface: it
requires the asphericity proof and Huebschmann's finite-order argument, not
only the Euler estimate for one disc.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace KazhdanHyp

open PresentedGroupRelatorReplay

universe u v

/-! ## A source-faithful finite-order localization interface -/

/-- An element of a free group is a proper power when it is an `n`th power
for some natural exponent `n >= 2`. -/
def RelatorIsProperPower {Generator : Type u} (r : FreeGroup Generator) : Prop :=
  ∃ z n, 2 ≤ n ∧ r = z ^ n

/-- Cubes give a direct nonempty model of the proper-power predicate. -/
theorem relatorIsProperPower_cube {Generator : Type u} (z : FreeGroup Generator) :
    RelatorIsProperPower (z ^ 3) :=
  ⟨z, 3, by norm_num, rfl⟩

/-- Every nonidentity element whose positive power is one forces one of a
specified family of obstructions.  For a presentation, the obstruction will
be that a defining relator is a proper power.

This is strictly more informative than torsion-freeness: it identifies a
finite relator index when torsion occurs.  Huebschmann's Theorem 3 supplies
this implication, together with the stronger divisibility and conjugacy
conclusions quoted in the module docstring. -/
def FiniteOrderForces
    (G : Type u) [Group G] (Index : Type v) (obstruction : Index → Prop) : Prop :=
  ∀ g : G, ∀ n : ℕ, 0 < n → g ^ n = 1 → g ≠ 1 →
    ∃ i, obstruction i

/-- The localization interface has the intended trivial-group model: the
nonidentity premise is impossible. -/
theorem finiteOrderForces_trivialModel
    (Index : Type v) (obstruction : Index → Prop) :
    FiniteOrderForces PUnit Index obstruction := by
  intro g n hn hpow hne
  exact (hne (Subsingleton.elim _ _)).elim

/-- The localization interface also holds for the rank-one free group, since
Mathlib proves that every free group has injective positive power maps. -/
theorem finiteOrderForces_freeGroupOneModel
    (Index : Type v) (obstruction : Index → Prop) :
    FiniteOrderForces (FreeGroup (Fin 1)) Index obstruction := by
  intro g n hn hpow hne
  have htf : IsPowerTorsionFree (FreeGroup (Fin 1)) :=
    IsPowerTorsionFree.of_isMulTorsionFree
  exact (hne (htf g n hn hpow)).elim

/-- The predicate is not vacuous: the two-element group cannot localize its
nontrivial torsion at an empty obstruction family. -/
theorem not_finiteOrderForces_twoGroup_empty :
    ¬ FiniteOrderForces (Multiplicative (ZMod 2)) PEmpty (fun _ ↦ False) := by
  intro h
  let tau : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  have htau_ne : tau ≠ 1 := by decide
  have htau_sq : tau ^ 2 = 1 := by decide
  obtain ⟨i, hi⟩ := h tau 2 (by norm_num) htau_sq htau_ne
  exact PEmpty.elim i

/-- Localization at an impossible obstruction family proves ordinary
torsion-freeness. -/
theorem isPowerTorsionFree_of_finiteOrderForces
    {G : Type u} [Group G] {Index : Type v} {obstruction : Index → Prop}
    (hloc : FiniteOrderForces G Index obstruction)
    (hno : ∀ i, ¬ obstruction i) : IsPowerTorsionFree G := by
  intro g n hn hpow
  by_contra hne
  obtain ⟨i, hi⟩ := hloc g n hn hpow hne
  exact hno i hi

/-! ## Exponent sums of positive triangular relators -/

section ExponentSums

variable {Generator : Type u} [DecidableEq Generator]

/-- The total exponent-sum homomorphism sends every free generator to `1` in
the additive infinite cyclic group. -/
def totalExponentHom : FreeGroup Generator →* Multiplicative ℤ :=
  FreeGroup.lift (fun _ ↦ Multiplicative.ofAdd 1)

/-- The exponent-sum homomorphism in one generator coordinate. -/
def generatorExponentHom (a : Generator) :
    FreeGroup Generator →* Multiplicative ℤ :=
  FreeGroup.lift (fun b ↦ Multiplicative.ofAdd (if b = a then 1 else 0))

/-- A positive triangular relator has total exponent sum three. -/
theorem totalExponentHom_relator
    (t : TriangularHodgeLayer.Triangle Generator)
    (hpositive : ∀ k, (t k).2 = true) :
    Multiplicative.toAdd (totalExponentHom (TriangularHodgeLayer.relator t)) = 3 := by
  simp [totalExponentHom, TriangularHodgeLayer.relator,
    TriangularHodgeLayer.letters_eq_three, word, FreeGroup.lift_mk, hpositive]

/-- The exponent sum in coordinate `a` is the number of the three positive
letters whose generator component equals `a`. -/
theorem generatorExponentHom_relator
    (a : Generator) (t : TriangularHodgeLayer.Triangle Generator)
    (hpositive : ∀ k, (t k).2 = true) :
    Multiplicative.toAdd
        (generatorExponentHom a (TriangularHodgeLayer.relator t)) =
      (if (t 0).1 = a then 1 else 0) +
        (if (t 1).1 = a then 1 else 0) +
          (if (t 2).1 = a then 1 else 0) := by
  simp [generatorExponentHom, TriangularHodgeLayer.relator,
    TriangularHodgeLayer.letters_eq_three, word, FreeGroup.lift_mk, hpositive]

/-- A positive length-three relator which is a proper power in the free group
is a cube of one signed generator.  First the total exponent sum shows that
the exponent divides `3`, so it equals `3`; then the coordinate of the first
letter shows that both other letters have the same generator component.
Positivity makes their sign components equal as well. -/
theorem positive_triangle_cube_of_relatorIsProperPower
    (t : TriangularHodgeLayer.Triangle Generator)
    (hpositive : ∀ k, (t k).2 = true)
    (hpower : RelatorIsProperPower (TriangularHodgeLayer.relator t)) :
    t 0 = t 1 ∧ t 1 = t 2 := by
  obtain ⟨z, n, hn, hrel⟩ := hpower
  have htotal := congrArg
    (fun r : FreeGroup Generator ↦ Multiplicative.toAdd (totalExponentHom r)) hrel
  rw [totalExponentHom_relator t hpositive, map_pow, toAdd_pow,
    nsmul_eq_mul] at htotal
  have hdivInt : (n : ℤ) ∣ (3 : ℤ) := by
    refine ⟨Multiplicative.toAdd (totalExponentHom z), ?_⟩
    simpa [mul_comm] using htotal
  have hdivNat : n ∣ 3 := Int.natCast_dvd_natCast.mp hdivInt
  have hn_three : n = 3 :=
    ((by norm_num : Nat.Prime 3).dvd_prime_two_le hn).mp hdivNat
  have hcoordinate := congrArg
    (fun r : FreeGroup Generator ↦
      Multiplicative.toAdd (generatorExponentHom (t 0).1 r)) hrel
  rw [generatorExponentHom_relator (t 0).1 t hpositive, map_pow,
    toAdd_pow, nsmul_eq_mul, hn_three] at hcoordinate
  by_cases h10 : (t 1).1 = (t 0).1
  · by_cases h20 : (t 2).1 = (t 0).1
    · constructor
      · apply Prod.ext
        · exact h10.symm
        · rw [hpositive 0, hpositive 1]
      · apply Prod.ext
        · exact h10.trans h20.symm
        · rw [hpositive 1, hpositive 2]
    · simp [h10, h20] at hcoordinate
      omega
  · by_cases h20 : (t 2).1 = (t 0).1
    · simp [h10, h20] at hcoordinate
      omega
    · simp [h10, h20] at hcoordinate
      omega

end ExponentSums

/-! ## The checked-table consequence -/

section CheckedTable

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- Every defining relator of a girth-eight table is not a proper power in the
free group.  This is the exact no-proper-power hypothesis in Huebschmann's
finite-order theorem. -/
theorem GirthEightChecks.relators_not_properPower
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (h : GirthEightChecks T d) (j : TriangleIndex) :
    ¬ RelatorIsProperPower (TriangularHodgeLayer.relator (T j)) := by
  intro hpower
  apply h.noCube j
  exact positive_triangle_cube_of_relatorIsProperPower (T j) (h.1 j) hpower

/-- Huebschmann's finite-order conclusion specialized to the defining
relators of one triangular presentation. -/
def FiniteOrderForcesRelatorProperPower
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  FiniteOrderForces (TriangularHodgeLayer.Presented T) TriangleIndex
    (fun j ↦ RelatorIsProperPower (TriangularHodgeLayer.relator (T j)))

/-- Finite-order localization and the girth-eight checks prove
torsion-freeness of the presented group. -/
theorem presented_isPowerTorsionFree_of_finiteOrderForcesRelatorProperPower
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (hchecks : GirthEightChecks T d)
    (hloc : FiniteOrderForcesRelatorProperPower T) :
    IsPowerTorsionFree (TriangularHodgeLayer.Presented T) :=
  isPowerTorsionFree_of_finiteOrderForces hloc hchecks.relators_not_properPower

end CheckedTable

/-! ## Universal geometric frontier -/

/-- The source-localization theorem closes the repository's universal
girth-eight torsion-freeness residual.  The hypothesis is left anonymous:
the named, model-tested geometric unit is
`FiniteOrderForcesRelatorProperPower T` for one presentation.

The `C(3)`--`T(8)` checks imply `C(3)`--`T(6)`; Huebschmann's Theorem 4 gives
asphericity, and Theorem 3 then gives the finite-order localization consumed
here. -/
theorem girthEightTorsionFree_of_localization
    (hloc :
      ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
        (_ : DecidableEq Generator) (_ : Nonempty Generator)
        (_ : Fintype TriangleIndex) (_ : DecidableEq TriangleIndex)
        (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
        GirthEightChecks T d → FiniteOrderForcesRelatorProperPower T) :
    GirthEightTorsionFree := by
  intro Generator TriangleIndex fg dg ng ft dt T d hchecks
  exact presented_isPowerTorsionFree_of_finiteOrderForcesRelatorProperPower
    hchecks (hloc Generator TriangleIndex fg dg ng ft dt T d hchecks)

end KazhdanHyp
end GroupApproximation
