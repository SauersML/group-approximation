---
rg: 2
id: stw99-lxxvi-finite-graph-pointwise-cu-proof
kind: route
title: Apply the idealwise K1-free one-dimensional Cu formula pointwise
target: stw99-lxxvi-finite-graph-fields-over-k1-trivial-pure-fibers
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Put `E=D tensor_min Z`.  Lin's stable-rank theorem, quoted as STW Theorem
21, gives stable rank one for the simple separable stably finite pure algebra
`D`.  The algebra `E` is again simple, separable, stably finite, and pure, so
it also has stable rank one.

The first-factor inclusion `D->E` is a KK-equivalence because `C->Z` is one.
Thus

```text
K_1(E)=K_1(D)=0.                                           (2)
```

Since `D` and `E` are simple, their only closed two-sided ideals are zero and
the whole algebra.  Equation (2) therefore verifies, for both coefficients,
the exact idealwise hypothesis

```text
K_1(I)=0 for every closed two-sided ideal I.                (3)
```

Antoine--Perera--Santiago, Theorem 3.4 in
[*Pullbacks, C(X)-algebras, and their Cuntz
semigroup*](https://arxiv.org/abs/1101.4776), states that if `Y` is second
countable, locally compact, Hausdorff, and one-dimensional and a separable
coefficient has stable rank one and satisfies (3), then fiber evaluation is
an isomorphism

```text
Cu(C_0(Y,B)) ~= Lsc(Y,Cu(B)).                              (4)
```

A finite graph meets the hypotheses on `Y`.  Applying (4) to `B=D` and
`B=E` gives (1).  The canonical tensor identification

```text
C(X,D) tensor_min Z ~= C(X,D tensor_min Z)=C(X,E)
```

uses nuclearity of `C(X)` and `Z`.  The isomorphisms in (4) are the
evaluation maps, so naturality identifies the first-factor map in (1) with

```text
f |-> (x |-> Cu(D->E)(f(x))).                              (5)
```

STW Proposition 23 says that `Cu(D)->Cu(E)` is an isomorphism because `D`
is simple, separable, stably finite, and pure.  Pointwise application of this
isomorphism is an isomorphism between the two `Lsc` semigroups.  Equations
(1) and (5) prove Cu-regularity.  Finally, Seth--Vilalta, Corollary 5.9 in
[*Continuous functions over a pure C*-algebra*](https://arxiv.org/abs/2602.14809),
proves independently that `C(X,D)` is pure for every compact metric `X` and
simple pure `D`.

The imported one-dimensional formula cannot simply be used after deleting
(3).  Antoine--Dadarlat--Perera--Santiago remove the `K_1` hypothesis for the
interval in Theorem 2.6 of
[*Recovering the Elliott invariant from the Cuntz
semigroup*](https://arxiv.org/abs/1109.5803), and treat the circle in Theorem
3.7 by retaining a separate projection-clutching summand.  Their Remark 3.9
exhibits a circle with an attached interval where pointwise Cuntz comparison
misses a nonzero `K_1` clutching class.  Thus the new deduction here is the
finite-graph Cu-regularity consequence under the precise published
idealwise `K_1` hypothesis; it does not assume an unavailable arbitrary-fiber
graph pullback formula.
