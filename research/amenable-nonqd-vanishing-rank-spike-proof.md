---
rg: 2
id: amenable-nonqd-vanishing-rank-spike-proof
kind: route
title: Cut a persistent norm defect at half height and apply Chebyshev to its singular values
target: amenable-nonqd-traces-have-vanishing-rank-norm-spikes
requires: []
artifacts:
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

If every pair `a,b` had

```text
||Phi_n(ab)-Phi_n(a)Phi_n(b)|| -> 0,
```

the same u.c.p. sequence, together with its assumed trace convergence, would
witness that `tau` is quasidiagonal.  Hence some pair has positive
operator-norm limsup.  Neither member is zero; rescale them to contractions,
choose `eta>0` below the resulting limsup, and pass to a subsequence on
which `||D_n||>=eta`.

Let `P_n=1_[eta/2,infinity)(|D_n|)`.  A largest singular value at least
`eta` makes `P_n` nonzero.  Functional calculus gives

```text
|D_n|^2 >= (eta/2)^2 P_n.
```

Taking normalized matrix traces yields the explicit spectral-tail bound

```text
tr(P_n) <= 4 tr(|D_n|^2)/eta^2
        = 4 ||D_n||_2^2/eta^2 -> 0.
```

There is also a sharper dimension estimate.  Since one singular value of
`D_n` is at least `eta`, its square contributes at least `eta^2` to the
unnormalized matrix trace.  Therefore

```text
||D_n||_2^2 = Tr(|D_n|^2)/d_n >= eta^2/d_n,
d_n >= eta^2/||D_n||_2^2 -> infinity.
```

Hilbert--Schmidt multiplicativity supplies both limits.  This proves all
assertions and uses no exactness, UCT, local lifting, or faithfulness.
