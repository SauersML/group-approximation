import GroupApproximation.GGT.KazhdanHypSingerReduction
import GroupApproximation.GGT.KazhdanHypSymplecticQuadrangleStrongRegular

/-!
# Cardinalities for the order-65 Singer reduction

The orbit-matrix search uses an order-65 permutation of the 585 points and
585 lines of `W(8)`.  Its nine point orbits and nine line orbits have length
65.  Compatible point-line pairs have 81 orbit roots, and an equivariant
triangle table has 27 triangle roots because `1755 = 27 * 65`.

`SingerOrbitEnumeration` is the count-level interface for these data.  It
also converts directly to the `CyclicOrbitCover` consumed by
`girthEightChecks_of_singer_orbits`; that theorem remains the source of the
root-check transport and is not repeated here.  The Boolean checks accept the
raw finite orbit maps emitted by the orbit-matrix search, so a future witness
can verify its 27 rows before the existing Singer reduction is applied.
-/

noncomputable section

namespace GroupApproximation
namespace KazhdanHyp

open scoped BigOperators

/-! ## One finite free cyclic orbit -/

abbrev SingerPeriod := Fin 65
abbrev SingerPointOrbitRep := Fin 9
abbrev SingerLineOrbitRep := Fin 9
abbrev SingerPairOrbitRep := Fin 81
abbrev SingerTriangleOrbitRep := Fin 27

/-- A finite enumeration of free order-65 cyclic orbits.  The equivalence
separates orbit roots and positions, and `iterate_from_root` identifies the
position with the corresponding Singer iterate. -/
structure SingerOrbitEnumeration {X Rep : Type*}
    [Fintype X] [Fintype Rep] (sigma : Equiv.Perm X) where
  orbit : Rep → SingerPeriod → X
  orbitEquiv : Rep × SingerPeriod ≃ X
  orbitEquiv_apply : ∀ r k, orbitEquiv (r, k) = orbit r k
  iterate_from_root : ∀ r k,
    (sigma ^[k.val]) (orbit r 0) = orbit r k

/-- A Singer orbit enumeration is exactly the cover shape consumed by the
existing equivariant reduction. -/
noncomputable def SingerOrbitEnumeration.toCyclicOrbitCover
    {X Rep : Type*} [Fintype X] [Fintype Rep]
    {sigma : Equiv.Perm X}
    (D : SingerOrbitEnumeration (Rep := Rep) sigma) :
    CyclicOrbitCover sigma Rep where
  root := fun r ↦ D.orbit r 0
  representative := fun x ↦ (D.orbitEquiv.symm x).1
  exponent := fun x ↦ ((D.orbitEquiv.symm x).2).val
  covers := by
    intro x
    let z := D.orbitEquiv.symm x
    have hz : D.orbitEquiv z = x := D.orbitEquiv.apply_symm_apply x
    rw [← hz]
    simp only [D.orbitEquiv.symm_apply_apply]
    rw [D.orbitEquiv_apply]
    exact D.iterate_from_root z.1 z.2

/-- No nonzero position in one enumerated Singer orbit fixes its root. -/
theorem SingerOrbitEnumeration.free_on_root
    {X Rep : Type*} [Fintype X] [Fintype Rep]
    {sigma : Equiv.Perm X}
    (D : SingerOrbitEnumeration (Rep := Rep) sigma)
    (r : Rep) {k : SingerPeriod} (hk : k ≠ 0) :
    (sigma ^[k.val]) (D.orbit r 0) ≠ D.orbit r 0 := by
  intro h
  have h' : D.orbitEquiv (r, k) = D.orbitEquiv (r, 0) := by
    calc
      D.orbitEquiv (r, k) = D.orbit r k := D.orbitEquiv_apply r k
      _ = (sigma ^[k.val]) (D.orbit r 0) := (D.iterate_from_root r k).symm
      _ = D.orbit r 0 := h
      _ = D.orbitEquiv (r, 0) := (D.orbitEquiv_apply r 0).symm
  have hpos : (r, k) = (r, 0) := D.orbitEquiv.injective h'
  exact hk (congrArg Prod.snd hpos)

/-! ## Generic orbit cardinalities -/

/-- The cardinality of an enumerated order-65 action is the number of roots
times 65. -/
theorem card_of_singerOrbitEnumeration
    {X Rep : Type*} [Fintype X] [Fintype Rep]
    {sigma : Equiv.Perm X}
    (D : SingerOrbitEnumeration (Rep := Rep) sigma) :
    Fintype.card X = Fintype.card Rep * 65 := by
  calc
    Fintype.card X = Fintype.card (Rep × SingerPeriod) :=
      Fintype.card_congr D.orbitEquiv.symm
    _ = Fintype.card Rep * 65 := by simp

/-- The raw finite map check used for an exported orbit table. -/
def singerOrbitBijectionCheck
    {X Rep : Type*} [Fintype X] [DecidableEq X]
    [Fintype Rep] [DecidableEq Rep]
    (orbit : Rep × SingerPeriod → X) : Bool :=
  decide (Function.Bijective orbit)

theorem singerOrbitBijectionCheck_eq_true_iff
    {X Rep : Type*} [Fintype X] [DecidableEq X]
    [Fintype Rep] [DecidableEq Rep]
    (orbit : Rep × SingerPeriod → X) :
    singerOrbitBijectionCheck orbit = true ↔ Function.Bijective orbit := by
  simp [singerOrbitBijectionCheck]

/-! ## The 9, 81, and 27 instances -/

/-- Nine free order-65 point orbits have 585 points. -/
theorem point_card_of_nine_singer_orbits
    {Point : Type*} [Fintype Point]
    {sigma : Equiv.Perm Point}
    (D : SingerOrbitEnumeration (Rep := SingerPointOrbitRep) sigma) :
    Fintype.card Point = 585 := by
  have h := card_of_singerOrbitEnumeration D
  norm_num at h ⊢
  exact h

/-- Nine free order-65 line orbits have 585 lines. -/
theorem line_card_of_nine_singer_orbits
    {Line : Type*} [Fintype Line]
    {sigma : Equiv.Perm Line}
    (D : SingerOrbitEnumeration (Rep := SingerLineOrbitRep) sigma) :
    Fintype.card Line = 585 := by
  have h := card_of_singerOrbitEnumeration D
  norm_num at h ⊢
  exact h

/-- The 81 compatible pair orbits have `81 * 65 = 5265` pairs. -/
theorem compatible_pair_card_of_81_singer_orbits
    {Pair : Type*} [Fintype Pair]
    {sigma : Equiv.Perm Pair}
    (D : SingerOrbitEnumeration (Rep := SingerPairOrbitRep) sigma) :
    Fintype.card Pair = 5265 := by
  have h := card_of_singerOrbitEnumeration D
  norm_num at h ⊢
  exact h

/-- An equivariant triangle table with 27 triangle orbits has
`27 * 65 = 1755` triangle rows. -/
theorem triangle_card_of_27_singer_orbits
    {TriangleIndex : Type*} [Fintype TriangleIndex]
    {sigma : Equiv.Perm TriangleIndex}
    (D : SingerOrbitEnumeration (Rep := SingerTriangleOrbitRep) sigma) :
    Fintype.card TriangleIndex = 1755 := by
  have h := card_of_singerOrbitEnumeration D
  norm_num at h ⊢
  exact h

/-! ## Named decidable checks for the orbit-matrix export -/

/-- The point orbit map emitted by the q = 8 search has nine roots. -/
def wEightPointOrbitCheck
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (orbit : SingerPointOrbitRep × SingerPeriod → Point) : Bool :=
  singerOrbitBijectionCheck orbit

theorem wEightPointOrbitCheck_eq_true_iff
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (orbit : SingerPointOrbitRep × SingerPeriod → Point) :
    wEightPointOrbitCheck orbit = true ↔ Function.Bijective orbit := by
  simp [wEightPointOrbitCheck, singerOrbitBijectionCheck]

/-- The line orbit map emitted by the q = 8 search has nine roots. -/
def wEightLineOrbitCheck
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (orbit : SingerLineOrbitRep × SingerPeriod → Line) : Bool :=
  singerOrbitBijectionCheck orbit

theorem wEightLineOrbitCheck_eq_true_iff
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (orbit : SingerLineOrbitRep × SingerPeriod → Line) :
    wEightLineOrbitCheck orbit = true ↔ Function.Bijective orbit := by
  simp [wEightLineOrbitCheck, singerOrbitBijectionCheck]

/-- The 81 pair roots in the JSON export are checked as a complete order-65
orbit enumeration. -/
def wEightPairOrbitCheck
    {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (orbit : SingerPairOrbitRep × SingerPeriod → Pair) : Bool :=
  singerOrbitBijectionCheck orbit

theorem wEightPairOrbitCheck_eq_true_iff
    {Pair : Type*} [Fintype Pair] [DecidableEq Pair]
    (orbit : SingerPairOrbitRep × SingerPeriod → Pair) :
    wEightPairOrbitCheck orbit = true ↔ Function.Bijective orbit := by
  simp [wEightPairOrbitCheck, singerOrbitBijectionCheck]

/-- The 27 triangle rows in the JSON export are checked as a complete
order-65 orbit enumeration before `girthEightChecks_of_singer_orbits` checks
the five link clauses. -/
def wEightTriangleOrbitCheck
    {TriangleIndex : Type*} [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (orbit : SingerTriangleOrbitRep × SingerPeriod → TriangleIndex) : Bool :=
  singerOrbitBijectionCheck orbit

theorem wEightTriangleOrbitCheck_eq_true_iff
    {TriangleIndex : Type*} [Fintype TriangleIndex] [DecidableEq TriangleIndex]
    (orbit : SingerTriangleOrbitRep × SingerPeriod → TriangleIndex) :
    wEightTriangleOrbitCheck orbit = true ↔ Function.Bijective orbit := by
  simp [wEightTriangleOrbitCheck, singerOrbitBijectionCheck]

/-! ## The 27-row pair cover -/

/-- Raw orbit-matrix rows, flattened by row and one of its three cyclic pair
positions.  Bijection onto `Fin 81` checks both that each row has three
distinct pair orbits and that the 27 rows cover every pair orbit once. -/
def wEightTrianglePairCoverCheck
    (pairOrbit : SingerTriangleOrbitRep × Fin 3 → SingerPairOrbitRep) : Bool :=
  decide (Function.Bijective pairOrbit)

theorem wEightTrianglePairCoverCheck_eq_true_iff
    (pairOrbit : SingerTriangleOrbitRep × Fin 3 → SingerPairOrbitRep) :
    wEightTrianglePairCoverCheck pairOrbit = true ↔ Function.Bijective pairOrbit := by
  simp [wEightTrianglePairCoverCheck]

end KazhdanHyp
end GroupApproximation
