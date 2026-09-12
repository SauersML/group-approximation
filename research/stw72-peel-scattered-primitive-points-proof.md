---
rg: 2
id: stw72-peel-scattered-primitive-points-proof
kind: route
title: Peel isolated primitive points into a continuous simple-layer series
target: stw72-scattered-primitive-spectrum-wpi-is-purely-infinite
requires:
  - stw72-transfinite-simple-layer-wpi-is-purely-infinite
artifacts:
  - research/artifacts/stw72-scattered-primitive-spectrum-collapse-audit-2026-08-30.md
---

Put `X=Prim(A)`.  We construct an increasing continuous family of open
subsets `(U_beta)` of `X`.  Start with `U_0=empty`.  If `U_beta!=X`, the
remainder

```text
F_beta=X\U_beta
```

is a nonempty subspace of the scattered space `X`, so it has an isolated
point `x_beta`.  Choose an open set `O_beta` of `X` satisfying

```text
O_beta intersect F_beta={x_beta}.
```

Then

```text
U_(beta+1)=U_beta union O_beta=U_beta union {x_beta}
```

is open.  At a limit ordinal `lambda`, put

```text
U_lambda=union_(beta<lambda) U_beta,
```

which is again open.  Each successor adds a new point, so the recursion
exhausts `X` at some ordinal `alpha` of cardinality at most `|X|`.

Use the standard ideal/open-set correspondence and let `I_beta` be the
closed ideal of `A` corresponding to `U_beta`.  Suprema of increasing ideals
correspond to unions of their open sets, hence at a limit ordinal

```text
I_lambda=closure(union_(beta<lambda) I_beta).
```

For a successor, the primitive spectrum of the subquotient is the locally
closed difference

```text
Prim(I_(beta+1)/I_beta)
  homeomorphic to U_(beta+1)\U_beta={x_beta}.
```

A nonzero C-star algebra whose primitive spectrum is a singleton is simple.
Indeed, the intersection of its primitive ideals is zero, so its unique
primitive ideal is zero; any nonzero proper ideal would be contained in a
primitive ideal obtained from an irreducible representation of the nonzero
quotient, a contradiction.  Thus every successor quotient in the displayed
filtration is simple.

We have constructed exactly the continuous transfinite composition series
required by `stw72-transfinite-simple-layer-wpi-is-purely-infinite`.
Applying that theorem proves that weak pure infiniteness of `A` collapses to
pure infiniteness.
