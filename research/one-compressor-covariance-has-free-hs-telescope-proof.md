---
rg: 2
id: one-compressor-covariance-has-free-hs-telescope-proof
kind: route
title: Only the wrap-around block is wrong, and it is one block in L
target: one-compressor-covariance-has-free-hs-telescope
requires: []
---

**`Pi_L` is a representation.**  Each `alpha^j` is an endomorphism of
`Lambda`, so each `rho o alpha^j` is a unitary representation on `C^d`, and
a direct sum of representations is a representation.  Injectivity of `alpha`
is not needed for this step; it is what makes the relation the ascending-HNN
one.

**The shift is covariant off one block.**  Let `T_L` send `H_j` to
`H_(j-1)`, so `T_L^(-1)` sends `H_j` to `H_(j+1)`, indices mod `L`.  For
`0 <= j <= L-1`,

```text
(T_L Pi_L(gamma) T_L^(-1))|_(H_j) = rho(alpha^(j+1)(gamma)),
```

where `j+1` is taken mod `L`, while

```text
Pi_L(alpha(gamma))|_(H_j) = rho(alpha^j(alpha(gamma))) = rho(alpha^(j+1)(gamma)),
```

with `j+1` taken as an integer.  For `j = 0,...,L-2` the two exponents agree
and the blocks are equal.  Only at `j = L-1` do they differ: the conjugate
gives `rho(alpha^0(gamma)) = rho(gamma)` because the shift wraps, whereas the
target gives `rho(alpha^L(gamma))`.  So the difference is supported on the
single block `H_(L-1)`, of dimension `d` inside the total dimension `Ld`.

**The rate.**  On that block the difference is `rho(gamma) - rho(alpha^L(gamma))`,
a difference of two unitaries of size `d`.  With `Tr` the unnormalized trace,
`Tr(u^* u) = d` for any `u in U(d)`, so by the triangle inequality in the
unnormalized Hilbert--Schmidt norm the block difference has

```text
Tr( (rho(gamma) - rho(alpha^L(gamma)))^* (rho(gamma) - rho(alpha^L(gamma))) )
   <= (sqrt(d) + sqrt(d))^2 = 4 d.
```

Normalizing by the total dimension `Ld`,

```text
|| T_L Pi_L(gamma) T_L^(-1) - Pi_L(alpha(gamma)) ||_2^2 <= 4d / (L d) = 4 / L,
```

hence the bound `2 / sqrt(L)`.  The dimension `d` cancels, which is the whole
point: the estimate is a *block count*, not a spectral estimate, so it is
uniform in `gamma` and free of any hypothesis on `rho`.
