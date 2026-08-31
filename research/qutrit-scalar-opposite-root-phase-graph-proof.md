---
rg: 2
id: qutrit-scalar-opposite-root-phase-graph-proof
kind: proof
title: Compute the transvection double coset from two affine leaf stabilizers
target: qutrit-scalar-opposite-root-is-diagonal-or-complete
requires:
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
  - qutrit-jacobson-residual-has-fixed-polar-gap
---

On a qutrit leaf `(u_1,u_2,s)`, an element `J^cZ_1^b` acts by

```text
(u_1,u_2,s) |-> (u_1,u_2,s+c-bu_1).
```

Its stabilizer depends only on `u_1` and is

```text
C_(u_1)={J^(bu_1)Z_1^b:b in F_3} isomorphic to C_3.    (QKG3)
```

Stabilizers for two different `u_1`-values intersect trivially, while
two leaves with the same value have the same stabilizer. The extra scalar
coordinate is fixed by all of `C`, so pairing it with a leaf gives that
leaf's order-three stabilizer.

We next identify the transvection intersection. Let `P` be a permutation
matrix on these coordinates and `k=1+E_ij`. A direct column calculation
shows

```text
kPk is a permutation matrix
if and only if P fixes i and j separately.              (QKG4)
```

Indeed, unless `P(j)=j`, the column which `P` sends to `j` acquires
two nonzero entries after left multiplication by `k`. Once `P(j)=j`,
the `j`-column of `kPk` has one nonzero entry only when `P(i)=i`.
The converse is immediate because such a `P` commutes with `k`.

If `c in C intersect kCk`, write `c=kc'k` with `c' in C`.
Both `c,c'` are permutation matrices, so `(QKG4)` makes `c'` fix
the two chosen coordinates. It then commutes with `k` and `c=c'`.
Conversely every common point stabilizer commutes with `k`. Therefore

```text
C intersect kCk=C_i intersect C_j.                      (QKG5)
```

Equation `(QKG3)` now gives the two possibilities for `H`.

It remains to compute the character blocks. For
`e_a=z_(C,chi_a)`, the standard finite-group intertwining calculation
says

```text
e_b k e_a=0
unless chi_a restricted to H equals chi_b restricted to H. (QKG6)
```

When the restrictions agree, double-coset expansion gives

```text
||e_b k e_a||_2^2=|H|/|C|^2=|H|/81.                    (QKG7)
```

For completeness, two terms `c_1kc_2` and `c_1'kc_2'` in the expansion
coincide precisely when the corresponding quotient lies in `H`.
There are `|H|` coherent collisions per double-coset coefficient when
`(QKG6)` holds; otherwise their character phases cancel.

If `H={1}`, every pair of restrictions agrees and `(QKG7)` gives
`(QKG1)`. If `H=C_(u_1)`, its generator can be taken as
`J^(u_1)Z_1`, and

```text
chi_a(J^(u_1)Z_1)=omega^(u_1+a).
```

The three restrictions are distinct, so `(QKG6)` permits exactly
`a=b`; then `(QKG7)` gives `1/27`. The extra-coordinate case uses
the same leaf stabilizer and has the identical conclusion. This proves the
diagonal-or-complete classification and the asserted branch no-go.
