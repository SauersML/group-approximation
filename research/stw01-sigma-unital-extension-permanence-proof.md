---
rg: 2
id: stw01-sigma-unital-extension-permanence-proof
kind: route
title: Turn ideal trace-linearity into square-seminorm centrality in the multiplier algebra
target: stw01-sigma-unital-extensions-preserve-qt-linearity
requires:
  - stw01-sigma-unital-cuts-have-quasitracial-idempotence
  - stw01-asymptotic-quasitracial-cuts-promote-linearity
artifacts:
  - research/artifacts/stw01-sigma-unital-extension-audit-2026-08-30.md
---

Fix a bounded `2`-quasitrace `tau` on `A`, and put `theta=tau|I`.  By the
ideal hypothesis, `theta` is a bounded trace.  Choose an increasing
positive-contractive approximate unit `(e_n)` for `I` as in
`stw01-sigma-unital-cuts-have-quasitracial-idempotence`.

We first verify the two square-seminorm conditions of
`stw01-asymptotic-quasitracial-cuts-promote-linearity`.  Since both `(e_n)`
and `(e_n^2)` are approximate units, the standard norm formula for a
positive functional gives

```text
theta(e_n) -> ||theta||,             theta(e_n^2) -> ||theta||.       (SUE1)
```

Also, functional calculus on `[0,1]` gives

```text
0 <= (e_n-e_n^2)^2 <= e_n-e_n^2.
```

Consequently

```text
tau((e_n-e_n^2)^2)
 <= theta(e_n)-theta(e_n^2) -> 0.                              (SUE2)
```

The commutator condition does not require norm quasicentrality.  The bounded
trace `theta` has its canonical finite tracial extension `tilde(theta)` to
`M(I)`, with `tilde(theta)(1)=||theta||`.  The multiplication action gives a
contractive unital star homomorphism `A -> M(I)` (possibly with a kernel),
which we use without changing notation.  From `(SUE1)`,

```text
tilde(theta)((1-e_n)^2)
 = ||theta||-2theta(e_n)+theta(e_n^2) -> 0.                    (SUE3)
```

For `a in A`, the tracial `2`-seminorm on `M(I)` and its triangle inequality
give, with `r_n=1-e_n`,

```text
||[e_n,a]||_(2,tilde(theta))
 = ||a r_n-r_n a||_(2,tilde(theta))
 <= ||a r_n||_2+||r_n a||_2
 <= 2||a|| tilde(theta)(r_n^2)^(1/2) -> 0.                   (SUE4)
```

Here the last estimate follows respectively from
`r_n a* a r_n <= ||a||^2 r_n^2` and tracially moving the factors in
`a* r_n^2 a`.  Since `[e_n,a] in I`, `(SUE4)` is exactly

```text
tau([e_n,a]*[e_n,a]) -> 0.
```

Finally `Her_A(e_n) subset I`, so `tau` restricts to a trace on every
hereditary head.  The quotient hypothesis supplies trace-linearity on
`A/I`.  Applying `stw01-asymptotic-quasitracial-cuts-promote-linearity`
shows that `tau` is a trace.  Since `tau` was arbitrary, the extension has
bounded-quasitrace linearity.

**Multiplier continuity audit.**  The canonical extension may be obtained
by extending the nondegenerate GNS representation of `I` to `M(I)` and
using the finite normal trace on its von Neumann closure.  For every
positive-contractive approximate unit `v_n`, positivity gives
`theta(v_n)->||theta||`; applying this also to the approximate unit
`(v_n^2)` proves `(SUE1)`.  Thus `(SUE3)` is an equality of finite numbers,
not an appeal to unproved strict continuity of an arbitrary functional on
`M(I)`.
