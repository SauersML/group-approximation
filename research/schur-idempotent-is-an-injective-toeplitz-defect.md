---
rg: 2
id: schur-idempotent-is-an-injective-toeplitz-defect
kind: claim
title: A Schur forbidden idempotent is an explicit Toeplitz defect without collapsing its packet algebra
artifacts:
  - research/artifacts/schur-toeplitz-root-defect-envelope-2026-08-20.md
distinct_from:
  schur-predicate-is-character-density-difference: that realizes the forbidden projection as a complex character-density difference inside a finite group algebra; this embeds the same idempotent over a finite splitting field as the defect of a one-sided inverse.
  toeplitz-head-tail-unital-self-embedding: that constructs a proper self-embedding of the bare algebraic Toeplitz ring; this attaches its defect to a prescribed nonzero proper Schur idempotent while keeping the packet algebra injective.
  schur-density-gap-has-no-direct-relator-certificate: that rules out killing a nonzero embedded density by an ordinary group-relator ideal; this keeps the density nonzero and makes it vanish only in directly finite quotient rings.
---

Let `B_f` be a fixed Schur--Clifford predicate packet with at least one
allowed and one forbidden selector character. Choose an odd finite splitting
field `k` for `B_f`, and let `P_f in k[B_f]` be the sum of the primitive
central idempotents belonging to the forbidden selector sectors. Thus

```text
0 != P_f != 1,                  P_f^2=P_f.                 (STD1)
```

Define the finitely presented unital `k`-algebra

```text
R_f=k[B_f]*_k k<x,y>/(yx=1, 1-xy=P_f).                    (STD2)
```

Then:

1. the canonical map `k[B_f]->R_f` is injective, so `P_f` remains nonzero;
2. every homomorphism from `R_f` to a finite ring, or more generally to a
   directly finite ring, kills `P_f`;
3. `R_f` is finitely presented and effective from the finite packet table.

For injectivity, take a countably infinite faithful `k[B_f]`-module `V`.
Both `P_f V` and `(1-P_f)V` are countably infinite-dimensional. Choose a
linear isomorphism `X:V->(1-P_f)V`; let `Y` be its inverse on `(1-P_f)V` and
zero on `P_f V`. Then

```text
YX=1,                  XY=1-P_f,                         (STD3)
```

and the faithful packet action together with `X,Y` gives a representation of
`R_f`. This proves clause 1. In a directly finite target, `yx=1` implies
`xy=1`; `(STD2)` then gives `P_f=0`, proving clause 2. Finite presentation is
immediate from the finite-dimensional packet algebra and the two displayed
relations.

This is an exact algebraic coupling of predicate orientation to a proper
corner. It does not yet control normalized-HS approximate representations:
turning clause 2 into a matricial microstate statement is precisely
`hs-schur-toeplitz-root-defect-collapse`.
