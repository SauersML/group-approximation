import GroupApproximation.Analysis.CStarPositiveOrder

/-!
# Pair-sum faces charge global commutators

This file formalizes the algebraic core of the balanced pair-sum argument.
For a logical pair, let `localLeft` and `localRight` be commuting involutions
obtained by exactifying one bounded local face, let `sharedLeft` and
`sharedRight` be the corresponding shared candidates, and write `leftError`
and `rightError` for their differences.  Then

```text
[sharedLeft, sharedRight]
  = leftError * sharedRight + localLeft * rightError
      - rightError * sharedLeft - localRight * leftError.
```

The four-term Cauchy--Schwarz estimate in the C-star order gives the local
Loewner bound by four copies of the incidence row square.  Summing over a
finite family of selected faces preserves the order.  Consequently any
operator-order congestion bound for those incidence squares immediately
charges the complete pair commutator Hamiltonian, uniformly in the matrix
dimension and in the number of logical coordinates.

This is the valid pair-sum charge inequality.  It does not assert the strict
joint descent step needed by the occurrence-Pauli route to construct a
non-hyperlinear group: Cairn records that additional step separately as
`parity-charge-or-green-divergence-has-strict-descent`.
-/

namespace GroupApproximation
namespace PairSumIncidence

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The multiplicative commutator, written additively in the ambient algebra. -/
def commutator (x y : A) : A :=
  x * y - y * x

/-- Four additive copies of a positive error Hamiltonian. -/
def fourCopies (x : A) : A :=
  (x + x) + (x + x)

/-- Four copies preserve the C-star order. -/
theorem fourCopies_mono {x y : A} (hxy : x ≤ y) :
    fourCopies x ≤ fourCopies y :=
  add_le_add (add_le_add hxy hxy) (add_le_add hxy hxy)

/-- The four-term Cauchy--Schwarz estimate in Loewner order.

This is obtained by applying the two-term parallelogram estimate three times.
The explicit four-copy spelling avoids introducing scalar-order compatibility
beyond the `StarOrderedRing` structure already used by the repository. -/
theorem star_four_sum_mul_self_le (a b c d : A) :
    star ((a + b) + (c + d)) * ((a + b) + (c + d)) ≤
      fourCopies
        (((star a * a + star b * b) + star c * c) + star d * d) := by
  have hab := OrderZero.star_add_mul_self_le (a := a) (b := b)
  have hcd := OrderZero.star_add_mul_self_le (a := c) (b := d)
  have hout := OrderZero.star_add_mul_self_le (a := a + b) (b := c + d)
  have hinner := add_le_add hab hcd
  calc
    star ((a + b) + (c + d)) * ((a + b) + (c + d)) ≤
        (star (a + b) * (a + b) + star (c + d) * (c + d)) +
          (star (a + b) * (a + b) + star (c + d) * (c + d)) := hout
    _ ≤
        (((star a * a + star b * b) + (star a * a + star b * b)) +
            ((star c * c + star d * d) + (star c * c + star d * d))) +
          (((star a * a + star b * b) + (star a * a + star b * b)) +
            ((star c * c + star d * d) + (star c * c + star d * d))) :=
      add_le_add hinner hinner
    _ = fourCopies
        (((star a * a + star b * b) + star c * c) + star d * d) := by
      simp only [fourCopies]
      abel

/-- The commutator decomposition against commuting exact local copies. -/
omit [PartialOrder A] [StarOrderedRing A] in
theorem commutator_eq_incidence_sum
    {localLeft localRight sharedLeft sharedRight leftError rightError : A}
    (hleftError : leftError = sharedLeft - localLeft)
    (hrightError : rightError = sharedRight - localRight)
    (hcommute : localLeft * localRight = localRight * localLeft) :
    commutator sharedLeft sharedRight =
      (leftError * sharedRight + localLeft * rightError) +
        (-(rightError * sharedLeft) + -(localRight * leftError)) := by
  simp only [commutator]
  calc
    sharedLeft * sharedRight - sharedRight * sharedLeft =
        (((sharedLeft - localLeft) * sharedRight +
            localLeft * (sharedRight - localRight)) +
          (-((sharedRight - localRight) * sharedLeft) +
            -(localRight * (sharedLeft - localLeft)))) +
          (localLeft * localRight - localRight * localLeft) := by
      noncomm_ring
    _ =
        ((sharedLeft - localLeft) * sharedRight +
          localLeft * (sharedRight - localRight)) +
          (-((sharedRight - localRight) * sharedLeft) +
            -(localRight * (sharedLeft - localLeft))) := by
      rw [hcommute, sub_self, add_zero]
    _ =
        (leftError * sharedRight + localLeft * rightError) +
          (-(rightError * sharedLeft) + -(localRight * leftError)) := by
      rw [← hleftError, ← hrightError]

/-- The data selected from one exactified pair-sum face. -/
structure ExactLocalPair (A : Type u) [CStarAlgebra A] where
  localLeft : A
  localRight : A
  sharedLeft : A
  sharedRight : A
  leftError : A
  rightError : A
  localLeft_star : star localLeft = localLeft
  localRight_star : star localRight = localRight
  sharedLeft_star : star sharedLeft = sharedLeft
  sharedRight_star : star sharedRight = sharedRight
  localLeft_sq : localLeft * localLeft = 1
  localRight_sq : localRight * localRight = 1
  local_commute : localLeft * localRight = localRight * localLeft
  leftError_eq : leftError = sharedLeft - localLeft
  rightError_eq : rightError = sharedRight - localRight

namespace ExactLocalPair

/-- The global commutator square attached to the selected logical pair. -/
def commutatorSquare (P : ExactLocalPair A) : A :=
  star (commutator P.sharedLeft P.sharedRight) *
    commutator P.sharedLeft P.sharedRight

/-- The symmetrized incidence row square paid by one exact local face. -/
def incidenceSquare (P : ExactLocalPair A) : A :=
  (((P.sharedRight * (P.leftError * P.leftError) * P.sharedRight +
      P.rightError * P.rightError) +
    P.sharedLeft * (P.rightError * P.rightError) * P.sharedLeft) +
    P.leftError * P.leftError)

/-- One exact local pair pays its shared commutator in operator order. -/
theorem commutatorSquare_le (P : ExactLocalPair A) :
    P.commutatorSquare ≤ fourCopies P.incidenceSquare := by
  have hleftErrorStar : star P.leftError = P.leftError := by
    rw [P.leftError_eq, star_sub, P.sharedLeft_star, P.localLeft_star]
  have hrightErrorStar : star P.rightError = P.rightError := by
    rw [P.rightError_eq, star_sub, P.sharedRight_star, P.localRight_star]
  have hleft :
      star (P.leftError * P.sharedRight) *
          (P.leftError * P.sharedRight) =
        P.sharedRight * (P.leftError * P.leftError) * P.sharedRight := by
    rw [star_mul, P.sharedRight_star, hleftErrorStar]
    noncomm_ring
  have hlocalLeft :
      star (P.localLeft * P.rightError) *
          (P.localLeft * P.rightError) =
        P.rightError * P.rightError := by
    rw [star_mul, hrightErrorStar, P.localLeft_star]
    calc
      (P.rightError * P.localLeft) * (P.localLeft * P.rightError) =
          P.rightError * (P.localLeft * P.localLeft) * P.rightError := by
        noncomm_ring
      _ = P.rightError * P.rightError := by
        rw [P.localLeft_sq]
        simp
  have hright :
      star (-(P.rightError * P.sharedLeft)) *
          (-(P.rightError * P.sharedLeft)) =
        P.sharedLeft * (P.rightError * P.rightError) * P.sharedLeft := by
    rw [star_neg, star_mul, P.sharedLeft_star, hrightErrorStar, neg_mul_neg]
    noncomm_ring
  have hlocalRight :
      star (-(P.localRight * P.leftError)) *
          (-(P.localRight * P.leftError)) =
        P.leftError * P.leftError := by
    rw [star_neg, star_mul, hleftErrorStar, P.localRight_star, neg_mul_neg]
    calc
      (P.leftError * P.localRight) * (P.localRight * P.leftError) =
          P.leftError * (P.localRight * P.localRight) * P.leftError := by
        noncomm_ring
      _ = P.leftError * P.leftError := by
        rw [P.localRight_sq]
        simp
  rw [commutatorSquare,
    commutator_eq_incidence_sum P.leftError_eq P.rightError_eq P.local_commute]
  simpa only [incidenceSquare, hleft, hlocalLeft, hright, hlocalRight] using
    star_four_sum_mul_self_le
      (P.leftError * P.sharedRight)
      (P.localLeft * P.rightError)
      (-(P.rightError * P.sharedLeft))
      (-(P.localRight * P.leftError))

/-- Summing the selected local-face inequalities charges the complete finite
pair Hamiltonian by four copies of the total incidence Hamiltonian. -/
theorem sum_commutatorSquare_le {kappa : Type*} (s : Finset kappa)
    (P : kappa → ExactLocalPair A) :
    (∑ k ∈ s, (P k).commutatorSquare) ≤
      fourCopies (∑ k ∈ s, (P k).incidenceSquare) := by
  calc
    (∑ k ∈ s, (P k).commutatorSquare) ≤
        ∑ k ∈ s, fourCopies (P k).incidenceSquare := by
      exact Finset.sum_le_sum fun k _ ↦ (P k).commutatorSquare_le
    _ = fourCopies (∑ k ∈ s, (P k).incidenceSquare) := by
      simp only [fourCopies, Finset.sum_add_distrib]

/-- **Bounded-congestion pair-sum theorem.**  If the selected face-incidence
row squares have an operator-order bound `H`, then four copies of `H` dominate
the complete pair commutator Hamiltonian. -/
theorem sum_commutatorSquare_le_of_boundedCongestion
    {kappa : Type*} (s : Finset kappa) (P : kappa → ExactLocalPair A) (H : A)
    (hcongestion : (∑ k ∈ s, (P k).incidenceSquare) ≤ H) :
    (∑ k ∈ s, (P k).commutatorSquare) ≤ fourCopies H :=
  (sum_commutatorSquare_le s P).trans (fourCopies_mono hcongestion)

end ExactLocalPair
end PairSumIncidence
end GroupApproximation
