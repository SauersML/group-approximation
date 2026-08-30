# STW XVIII/XXIII/XXVI: finite tracial-boundary audit (2026-08-30)

## Established cells

This audit records two published theorems and one formal consequence.

1. If `A` is simple, separable, unital, nuclear, and non-elementary, its
   extreme tracial boundary is nonempty, compact, and finite-dimensional,
   and `A` has strict comparison, then `A` is Jiang--Su stable.  This is the
   finite-boundary case of STW Problem XVIII.
2. If `A` is unital, simple, separable, exact, stably finite, and
   non-elementary and has finitely many extreme tracial states, then every
   strictly positive lower-semicontinuous affine function on `QT(A)` is the
   rank of a positive element of `A tensor K`.  Exactness identifies
   quasitraces with traces.  This is a finite-boundary case of STW Problem
   XXIII with no stable-rank or comparison hypothesis.
3. Under the hypotheses of STW Problem XXVI, compact finite-dimensional
   extreme tracial boundary makes Cuntz-semigroup Jiang--Su regularity imply
   algebraic Jiang--Su stability: Cuntz-semigroup regularity gives strict
   comparison, and item 1 applies.

## Primary sources and exact hypothesis match

Andrew Toms, Stuart White, and Wilhelm Winter,
[*Z-stability and finite dimensional tracial boundaries*](https://arxiv.org/abs/1209.3292),
International Mathematics Research Notices 2015, no. 10, 2702--2727,
prove that a simple separable unital nuclear non-elementary C-star algebra
whose tracial state space has nonempty compact extreme boundary of finite
covering dimension is Jiang--Su stable whenever it has strict comparison.
The result is stated in the abstract and obtained from their uniformly
tracially large order-zero maps together with the Matui--Sato absorption
criterion.  A singleton extreme boundary is the dimension-zero special
case, so this theorem supplies the final absorption step in the real-rank-
zero XXV argument without any separate lifting assertion.

Aaron Tikuisis and Andrew Toms,
[*On the structure of the Cuntz semigroup in (possibly) nonunital
C-star-algebras*](https://arxiv.org/abs/1210.2235), Canadian Mathematical
Bulletin 58 (2015), no. 2, 402--414, Corollary 4.4, prove that the rank map is onto
for a unital simple C-star algebra with finite nonempty extreme tracial
boundary.  Their Section 4 construction does not assume strict comparison.
For the Cairn claim we add exactness, so Haagerup's theorem gives
`QT(A)=T(A)` and the source's trace-rank conclusion is literally the
quasitracial conclusion asked for in Problem XXIII.  Separability,
stable finiteness, and non-elementarity are retained to stay inside the STW
problem's ambient class, although the cited rank theorem itself needs less.

## Logical boundaries

Neither imported result settles its full STW problem.

- Compactness and finite covering dimension of the extreme tracial boundary
  are decisive extra hypotheses in the XVIII theorem.  Toms's 2026 AH
  counterexample to universal uniform property Gamma prevents replacing
  this finite-boundary input by an automatic uniform-Gamma assertion.
- Finiteness of the extreme trace set is decisive in the XXIII theorem.
  The arbitrary wild-simplex selection problem remains open, as does the
  nonexact passage from traces to all quasitraces.
- The XXVI consequence inherits exactly the same boundary restriction; it
  does not prove the unrestricted Cuntz-semigroup-to-algebra absorption
  implication.
