---
rg: 2
id: qutrit-two-to-one-phase-graph-requires-central-line-twist
kind: claim
title: A qutrit two-to-one phase graph requires an asymmetric central-line twist
artifacts:
  - research/qutrit-first-stk-word-central-line-proof.md
distinct_from:
  qutrit-shortest-tk-word-graphs-are-diagonal-or-complete: that exhausts the dihedral T/opposite-root word ball by matrix calculation; this gives the general character criterion and adds the independent S-root closure.
  qutrit-scalar-opposite-root-is-diagonal-or-complete: that treats one scalar transvection; this identifies the only subgroup-intersection shape which could ever produce the desired two-to-one graph.
  qutrit-jacobson-residual-has-fixed-polar-gap: that supplies the numerical terminal after one complement branch is authenticated; this states the exact group-theoretic twist a word must provide to authenticate such a branch.
---

Let `C=<J,Z_1>` and let

```text
chi_a(J)=omega,          chi_a(Z_1)=omega^a,
e_a=z_(C,chi_a),         a in F_3.
```

For an ambient group element `g`, put

```text
H=C intersect gCg^(-1),        H'=g^(-1)Hg.
```

A block `e_b g e_a` is nonzero exactly when

```text
chi_b|_H=(chi_a after Ad(g^(-1)))|_H.                   (QCT1)
```

If `|H|=3`, the three restrictions of the `chi_a` to `H` are
all equal exactly when `H=<J>`; otherwise they are pairwise distinct.
The same dichotomy holds on `H'`. Consequently a phase graph with two
source phases feeding only one target phase can occur only in the asymmetric
case

```text
one of H,H' is <J>, and the other is a noncentral line. (QCT2)
```

Trivial intersections give the complete graph. Equal noncentral lines, or
two noncentral lines related by conjugation, give a matching. Two central
lines give a complete or empty graph. None of those patterns is
Hall-deficient on `R=e_0+e_1`.

Now add the first independent S-root to the alternating package:

```text
s=x_13(S),        t=x_23(T),        k=x_31(1).
```

For every word/value in the bounded closure table

```text
s,t,k, st, sk,ks, [s,k], tk,kt, [t,k],
[[t,k],s]=x_23(1),
```

and for every constant-Weyl conjugate of the whole active block, the
intersection `H` is a common point stabilizer of the active qutrit leaves,
and `g` centralizes it. Hence `H'=H` is either trivial or a noncentral
order-three line. No word in this first two-symbol closure satisfies
`(QCT2)`; all of its qutrit phase graphs are complete or matchings.

Thus distinguishing `1,S,T,ST` and consuming `TS=1` in the first
nested commutator still does not create the desired two-to-one selector.
The smallest eligible continuation must twist the central qutrit line
itself into a leaf-stabilizer line, or obtain branch deletion from an
analytic raw-residual compression not represented by the group-word phase
graph. Adding further local Weyl conjugates only permutes the active
coordinates and does not change this conclusion.
