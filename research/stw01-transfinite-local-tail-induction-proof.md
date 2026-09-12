---
rg: 2
id: stw01-transfinite-local-tail-induction-proof
kind: route
title: Split one ambient quasitrace at successors and use norm continuity at limits
target: stw01-transfinite-qt-linearity-filtrations
requires:
  - stw01-extensions-preserve-qt-linearity
artifacts:
  - research/artifacts/stw01-transfinite-linearity-audit-2026-08-30.md
---

Fix a bounded `2`-quasitrace `tau` on `A`.  We prove by transfinite
induction that its restriction to every `I_alpha` is a trace.  The assertion
at `alpha=0` is empty.

Suppose first that `tau|I_alpha` is a trace.  Choose an arbitrary
positive-contractive approximate-unit net `(e_lambda)` for `I_alpha`.
Apply the net-splitting construction of
`stw01-extensions-preserve-qt-linearity` to this one quasitrace in the
ambient unital algebra `A`.  The multiplier extension of the finite trace
`tau|I_alpha` gives

```text
tau((e_lambda-e_lambda^2)^2) -> 0,
tau([e_lambda,a]*[e_lambda,a]) -> 0       (a in A).
```

A cofinal ultrafilter therefore turns `(e_lambda)` into a central projection
`q` in the coordinate quasitracial quotient.  For self-adjoint `a in A`, the
same calculation gives an exact decomposition

```text
tau(a)=rho_alpha(a)+sigma_alpha(a),                     (TF1)
```

where

```text
rho_alpha(a)=lim_omega tau(e_lambda a e_lambda)
```

is linear because every compression belongs to `I_alpha`, while
`sigma_alpha` is a bounded `2`-quasitrace which vanishes on `I_alpha` and
factors through `A/I_alpha`.

Restrict `(TF1)` to `I_(alpha+1)`.  The induced tail on
`I_(alpha+1)/I_alpha` is a trace by the successor hypothesis, and the head
is already linear.  Hence `tau|I_(alpha+1)` is a trace.  Notice that no
quasitrace on the nonunital ideal `I_(alpha+1)` is extended: the entire
argument follows the fixed ambient `tau`.

Now let `lambda<=gamma` be a limit ordinal and suppose the restrictions are
traces below `lambda`.  Given self-adjoint `x,y in I_lambda`, approximate
them simultaneously by self-adjoint `x_beta,y_beta in I_beta` for one
`beta<lambda`; the chain is linearly ordered and its union is dense.
Bounded quasitraces on the unital algebra `A` are norm-continuous on the
self-adjoint part, so

```text
tau(x+y)=lim tau(x_beta+y_beta)
        =lim (tau(x_beta)+tau(y_beta))
        =tau(x)+tau(y).
```

Thus `tau|I_lambda` is a trace.  Transfinite induction reaches
`I_gamma=A`, proving the theorem.

**Trust boundary.**  The only successor calculation is the already proved
arbitrary-net splitting, used locally on one layer.  The limit step selects
no cofinal sequence: for each finite packet and tolerance, density supplies
one earlier stage containing simultaneous approximants.
