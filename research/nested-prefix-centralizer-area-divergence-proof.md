---
rg: 2
id: nested-prefix-centralizer-area-divergence-proof
kind: route
title: Turn exponent-two clique triangles into a fixed centralizer section
target: nested-prefix-clique-forces-centralizer-area-divergence
requires:
  - leavitt-nested-prefix-conjugacy-clique
  - finite-mark-centralizer-commutator-area-is-proper
---

Write `e_m=s_(0^m)t_(0^m)` and use the elementary-matrix quotient to read
root coefficients faithfully.  From `(NCD1)`,

```text
c_m=x_12(1+e_m).
```

Thus `c_1=x_12(s_1t_1)` is nontrivial, and all `c_m` commute and have order
two.  For distinct `m,n>=2`,

```text
c_m^(-1)c_n=x_12(e_m+e_n).                            (NCP1)
```

The coefficient in `(NCP1)` is nonzero and is orthogonal to `s_1t_1`, so
it is neither `0` nor the coefficient of `c_1`.  Consequently the `c_m`,
`m>=2`, represent distinct cosets in `C_Delta(c_1)/<c_1>`.

Assume the proposed edge bound is `A`, and let `D=Area(z^2)`, a fixed
constant.  If a word `u` has an area-`A` certificate that it is conjugate
to `z`, two copies of that certificate and one filling of `z^2` give

```text
Area(u^2)<=2A+D.                                       (NCP2)
```

Apply `(NCP2)` to the three edges `(0,1)`, `(0,m)`, and `(1,m)`.  Their
differences are respectively

```text
c_1,                     c_m,                     c_1^(-1)c_m.
```

The three square fillings turn the word `[c_1,c_m]` into the square of
`c_1^(-1)c_m` after replacing inverse occurrences using `c_1^2` and
`c_m^2`.  This uses only a fixed number of copies of the three diagrams, so

```text
Area([c_1,c_m])<=C_A
```

for a constant depending on `A`, `D`, and the presentation but not on `m`.
The preceding distinct-coset calculation now contradicts properness of
commutator area on `C_Delta(c_1)/<c_1>`.  Hence no uniform edge bound exists.
