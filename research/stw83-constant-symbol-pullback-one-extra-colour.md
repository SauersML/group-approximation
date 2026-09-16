---
rg: 2
id: stw83-constant-symbol-pullback-one-extra-colour
kind: claim
title: Constant-symbol pullbacks of compact fields cost at most one extra colour
artifacts:
  - research/artifacts/stw99-constant-symbol-pullback-2026-09-16.md
distinct_from:
  stw83-canonical-circle-is-constant-symbol-pullback: that identifies one graph family as a constant-symbol pullback; this is a general nuclear-dimension estimate for every constant-symbol pullback with any base space and any quotient of finite nuclear dimension.
  stw83-canonical-circle-toeplitz-dimension-two-bound: that is the value range for the canonical circle-by-circle family only; this theorem implies it and also covers Kirchberg and other quotients.
  stw81-af-fibre-fields-have-base-bound: that bounds C0-fields with AF fibres over a base; this bounds a non-central extension whose quotient is constant over the base and is not a field over it.
---

Let `X` be compact metrizable with `n=dim X<infinity`, let `H` be separable
and infinite-dimensional, and let `K=K(H) subseteq D subseteq B(H)` be a
separable C\*-algebra whose quotient `B=D/K` has `d=dim_nuc(B)<infinity`.
Put

```text
A_X(D) = C(X,K) + D tensor 1     inside C(X,B(H)).
```

This is a C\*-algebra, and there is an extension

```text
0 -> C(X,K) -> A_X(D) -> D/K -> 0.
```

Then

```text
max(n,d) <= dim_nuc(A_X(D)) <= max(n,d)+1.                     (1)
```

The generic extension estimate gives only `n+d+1`.  No `O_infinity`-stability
of `B` and no fullness of the extension is assumed.  The saving comes from
two features of the constant symbol:
* in the quasicentral three-piece decomposition, the transition band takes
  values in a fixed finite-dimensional algebra of constants;
* the quotient colours can be made exactly order zero in a hereditary
  subalgebra orthogonal to the inner corner `M_R(C(X))`, so they share
  colours with it.
