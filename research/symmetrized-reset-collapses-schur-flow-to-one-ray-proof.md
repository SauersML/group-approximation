---
rg: 2
id: symmetrized-reset-collapses-schur-flow-to-one-ray-proof
kind: route
title: Solve the child restriction equations after complete type balance
target: symmetrized-reset-collapses-schur-flow-to-one-ray
requires:
  - translation-symmetrized-schur-child-reset
  - translation-symmetrized-full-schur-reset
  - oriented-schur-child-branching-identity
  - shared-overlap-controls-packet-multiplicity-vector
---

The full reset balances selector spaces and independently flips both corrected
radical signs. For `f(x)=1`, `(OCB1)` says the unique full-packet simple `T_x`
restricts as

```text
T_x downarrow_C_f = sigma_(x,+) direct_sum sigma_(x,-).
```

No other full-packet simple lies over `x`.

For `f(x)=0`, the sector algebra is
`M_D(C) tensor C[(C_2)^2]`, so there are four full-packet simples. The
independent corrected `P` and `Q` flips act transitively on them. If the common
selector-space dimension is `h`, the active multiplicity is `h/(2D)` and
each inactive multiplicity is `h/(4D)`. Nonconstancy supplies an inactive
sector, so `n=h/(4D)` is integral and gives `(SRC6)`. This proves the
one-dimensionality of the full-reset restriction cone.

Every one of the `2^(k+1)` child types has multiplicity `2n`, giving
`2^(k+2)n`. The number of full-packet simples counted with multiplicity is
`2K_1n+4K_0n`, and the difference is `2K_1n`. Hilbert dimension is

```text
K_1(2n)(2D)+K_0(4n)D=4D(K_1+K_0)n=2^(k+2)Dn,
```

which proves `(SRC7)` and exhibits the scalar stationary compensation.

For the approximate statement, exactify the one fixed finite table `Rhat_f`.
The correction changes its named matrices on only controlled normalized
dimension, and restriction of the exact table to `B_f` lies on the
full-reset ray just computed. Equation `(OMV1)` converts the correction loss
to weighted type-vector discrepancy. Pulling through the fixed finite
restriction equations changes the constant only by a packet-dependent
factor, giving `C sqrt(E)`.
