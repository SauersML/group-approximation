# STW Problem X(1): factorial-witness reduction audit (2026-08-30)

## Result and graph boundary

The existing X(1) graph was checked before adding the new reduction.  Its
closest results were:

- `directed-unions-preserve-trace-approximations`, which gives a separable
  counterexample but does not alter the trace;
- `ideal-central-components-retain-an-amenable-nonqd-witness`, which cuts a
  trace into two central ideal components but does not make either component
  extreme; and
- `exact-gns-kernel-amenability-reduction`, which makes a specified trace
  faithful on its GNS quotient under exactness but does not make it
  factorial.

The new theorem combines compact convex geometry with those two reductions.
It shows that every counterexample has a separable factorial witness, and
that an exact counterexample has a faithful exact factorial witness whose
GNS closure is `R`.  It does not use or repackage
`stw09-jointly-faithful-mf-traces-force-mf`: that theorem derives an MF
algebra from a family of MF traces, whereas this theorem selects one extreme
amenable non-QD trace and never assumes an operator-norm MF model exists.
The concurrent Problem VII theorem
`stw07-primitive-mf-traces-force-quasidiagonality` applies that MF-separation
mechanism to primitive quotients of an algebra.  It neither selects an
individual amenable trace nor yields the factorial counterexample normal form
proved here.

## Source and status screen

The same-day primary-source audit in
`stw10-amenable-trace-frontier-2026-08-30.md` records Problem X(1) as open and
checks Brown's memoir, the exact-UCT theorems, the cone theorem, and the
newer homotopy-domination result.  Brown's
[Invariant means and finite representation theory of C*-algebras](https://arxiv.org/abs/math/0304009)
is the source for the amenable-trace face and locally reflexive GNS
hyperfiniteness inputs used here.  No source found in the existing graph
states the factorial-witness reduction.

## Proof audit and the load-bearing exactness fence

For separable `B`, the amenable traces form a weak-star compact face `K` of
`T(B)`, while QD traces form a weak-star closed convex subset `Q`.  If all
extreme points of `K` lay in `Q`, Krein--Milman would put all of `K` in `Q`.
Thus an amenable non-QD trace forces an extreme amenable non-QD trace.
Faciality makes this point extreme in all of `T(B)`, hence factorial.

There are two possible overclaims, both excluded in the route:

1. Amenability by itself does **not** make the GNS algebra hyperfinite for an
   arbitrary nonexact C-star algebra.  The general conclusion is only a
   factorial amenable witness.  Hyperfiniteness is invoked after exactness
   passes to the separable subalgebra.
2. Having GNS closure `R` does not identify the C-star algebra with `R` and
   does not transfer QD between them.  Therefore this theorem neither proves
   nor follows from STW Problem X(2), which asks whether the trace on `R`
   itself is QD.

Under exactness, the factorial GNS closure is hyperfinite with separable
predual.  A finite-dimensional factor would make the trace QD by the constant
GNS homomorphism, so the only remaining factor is `R`.  Passing to the GNS
quotient uses the established exact local-lifting theorem; QD of the quotient
trace would pull back, so non-QD survives.  This proves the faithful exact
normal form without asserting any nonexact quotient descent.
