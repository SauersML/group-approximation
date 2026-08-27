---
rg: 2
id: finite-local-schur-extension-preserves-mass-proof
kind: route
title: Clear the finitely many context divisibility constraints by one amplification
target: finite-local-schur-extension-preserves-forbidden-mass
requires:
  - predicate-rank-gate-doubles-restriction-multiplicity
---

Fix a context `c`.  Simultaneously diagonalize its commuting selector
involutions.  On a selector character `x`, the packet theorem prescribes one
finite-dimensional spin module of dimension

```text
d_(c,x)=2^(N_c+f_c(x)).                                 (FSEP1)
```

If the original `x`-eigenspace has multiplicity `m_(c,x)`, then after
amplification by `L` it has multiplicity `L m_(c,x)`.  Choose one positive
integer `L` divisible by every `d_(c,x)` occurring for every context and
character.  There are only finitely many.  Decompose each amplified selector
eigenspace into `d_(c,x)`-dimensional packet blocks and put the required spin
representation on every block.  Packet generators belonging to different
contexts are unrelated, so these choices coexist on the same amplified
Hilbert space.  This proves exact extension.

For every selector polynomial `a`,

```text
tr_(dL)(pi(a) tensor I_L)=tr_d(pi(a)).                 (FSEP2)
```

In particular every forbidden atom `F_c`, and hence their weighted sum, has
the same normalized trace before and after extension.  This proves `(FSE3)`.

For the counterexample choose an allowed character `x_0` and forbidden
character `x_1`.  The direct sum of `n-k` copies of `x_0` and `k` copies of
`x_1` has `q=k/n`.  Rational values `k/n` occur arbitrarily close to zero,
while every selector relation is exact.  The extension above makes all local
packet rows exact and preserves `q`, proving the failure of `(FSE4)`.

