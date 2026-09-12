---
rg: 2
id: directed-unions-preserve-tracial-strict-comparison-proof
kind: route
title: Transport a dimension gap to one stage using three quantitative cutdowns
target: directed-unions-preserve-tracial-strict-comparison
requires: []
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

Let `a,b` be positive elements of `A tensor K` satisfying

```text
d_tau(a) < d_tau(b).                                  (1)
```

We show `(a-epsilon)_+ <=_Cu b` for every `epsilon>0`.  Since
`d_tau(b)=sup_{t>0} d_tau((b-t)_+)`, choose `gamma>0` so small that

```text
2 gamma < epsilon,
d_tau(a) < d_tau((b-3 gamma)_+).                      (2)
```

The union of the matrix algebras over the `A_i` is dense in `A tensor K`.
After enlarging one index, choose positive `a_i,b_i` in the same matrix
algebra over `A_i` such that

```text
||a-a_i|| < gamma,    ||b-b_i|| < gamma.
```

Put `x=(a_i-gamma)_+` and `y=(b_i-2 gamma)_+`.  The standard Cuntz
perturbation lemma gives

```text
(a-2 gamma)_+ <=_Cu x <=_Cu a,
(b-3 gamma)_+ <=_Cu y <=_Cu b.                        (3)
```

Compatibility of the traces and (2)--(3) imply, already at stage `i`,

```text
d_{tau_i}(x) <= d_tau(a)
             < d_tau((b-3 gamma)_+)
             <= d_{tau_i}(y).
```

Strict comparison in `A_i` yields `x <=_Cu y`.  Combining this with (3) and
`2 gamma<epsilon` gives

```text
(a-epsilon)_+ <=_Cu (a-2 gamma)_+ <=_Cu x
                <=_Cu y <=_Cu b.
```

As this holds for every `epsilon>0`, the cutdown characterization of Cuntz
subequivalence gives `a <=_Cu b`, proving strict comparison in `A`.

**Trust boundary.**  The only standard input is the quantitative perturbation
fact `||c-d||<eta => (c-(t+eta))_+ <=_Cu (d-t)_+`; all uses and constants are
displayed.  No continuity theorem for the abstract Cuntz-semigroup functor is
being assumed.
