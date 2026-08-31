---
rg: 2
id: mikhailova-color-escape-proof
kind: route
title: Count repeated labels among finitely many quotient translates
target: mikhailova-color-code-must-escape-finite-palettes
requires:
  - mikhailova-left-right-soficity-is-one-color-code
---

Fix words `w_1,...,w_m` with pairwise distinct images in `H`, and
define random variables on the uniform probability space `A_n` by

```text
Y_i(a)=c_n(sigma_n(w_i)^(-1)a).
```

Because `sigma_n(w_i)` is a permutation, every `Y_i` has exactly the
same distribution `mu_n` as `c_n`.

For `i != j`, change variables by `sigma_n(w_i)^(-1)`.  The equality
probability `Pr[Y_i=Y_j]` becomes a root-color agreement coefficient
for the nonkernel word `w_j^(-1)w_i` (up to replacing it by its inverse,
which does not change whether its image in `H` is trivial).  The
one-color-code criterion therefore gives

```text
Pr[Y_i=Y_j] -> 0.                                      (MCP7)
```

Fix any color set `C` with `|C|<=K`, and at a point `a` let

```text
Z(a)=|{i:Y_i(a) in C}|.
```

Among the `Z(a)` entries taking values in a set of size at most `K`,
the number of equal pairs is at least `Z(a)-K`.  Equivalently,

```text
Z(a) <= K + sum_{i<j} 1_(Y_i(a)=Y_j(a)).               (MCP8)
```

Taking expectations and using the common marginal gives

```text
m mu_n(C)
 <= K + sum_{i<j} Pr[Y_i=Y_j]
 <= K + binom(m,2) epsilon_n.
```

Division by `m` is exactly `(MCE2)`.  The bound is uniform over all
sets `C` of size at most `K`, even when `C=C_n` depends on `n`.
First take the witnessing limit, so `epsilon_n->0`, and then take
`m` arbitrarily large.  Since `H` is infinite, such pairwise distinct
quotient words exist for every `m`.  This proves `(MCE1)`.

In particular, the largest atom of `mu_n` tends to zero and the number
of colors carrying nonzero mass tends to infinity.  This conclusion uses
only equality of labels, so it is invariant under arbitrary levelwise
renaming of the palette.
