---
rg: 2
id: stw63-af-bidual-return-obstruction-proof
kind: route
title: Preserve an antisymmetric K-zero class while the bidual sees only dimension
target: stw63-generic-bidual-return-fails-for-af
requires: []
---

Take the stationary unital AF system

```text
B = lim_n (M_(3^n) directSum M_(3^n)),
K_0 connecting matrix = [[2,1],[1,2]].                 (1)
```

The matrix is primitive, so `B` is simple.  Its unique normalized trace has
equal weights on the two summands.  At a stage with matrix size at least
three, choose rank-one projections `p` and `q` in the first and second
summands.  Then `tau(p)=tau(q)`.  But

```text
[[2,1],[1,2]] (e_1-e_2)=e_1-e_2,
```

so `[p]-[q]` survives at every later stage and is nonzero in `K_0(B)`.
The projections `p,q,1-p,1-q` are nonzero and therefore full in simple `B`.

Put `M=B**` and split it by its finite central projection `z`.  On `zM`, let
`T` be the center-valued trace.  For every normal positive functional `f` on
the center, `(f T)|_B` is a bounded trace and hence a scalar multiple of the
unique `tau`.  Equality of the scalar traces of `p,q`, and of their
complements, therefore implies

```text
T(zp)=T(zq),       T(z(1-p))=T(z(1-q)).                (2)
```

Finite von Neumann comparison turns (2) into equivalences.

On `(1-z)M`, finite-sum fullness in `B` gives a finite `m` with the central
unit subequivalent to `m` copies of each of `p,q,1-p,1-q`.  In every
properly infinite central summand this forces each such projection to be
properly infinite and equivalent to the central unit: finite amplification
of a finite projection would remain finite, while a properly infinite full
projection absorbs its finite amplification.  This finite-fullness step is
what prevents any illicit projection-cardinality inference.  Combining with
(2) gives

```text
p equivalent q,       1-p equivalent 1-q              (3)
```

in `M`.  The two partial isometries in (3) sum to a unitary `w in M` with
`wpw^*=q`.

Define `alpha,beta:C^2->B` by the decompositions `(p,1-p)` and `(q,1-q)`.
They are unitarily conjugate in `B**`.  If they were approximately unitarily
equivalent in `B`, some unitary would move `p` within norm less than one of
`q`; close projections are unitarily equivalent, contradicting
`[p] != [q]` in `K_0(B)`.  Standard AF permanence supplies all of the listed
regularity properties.
