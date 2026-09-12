---
rg: 2
id: mersenne-binary-h1-finite-audit-proof
kind: route
title: Enumerate cosets and eliminate the two cubic parity matrices exactly
target: first-mersenne-iwahori-levels-have-zero-binary-h1
requires:
  - proper-torus-diagonal-code-is-incomplete-cover-curl
  - linear-cocycle-dimension-forces-phase-countersequence
---

The artifact performs the following finite operations.

First it represents a matrix in `SL_2(Z/mZ)/{+-I}` by the
lexicographically smaller of a determinant-one matrix and its negative.
Breadth-first enumeration from `x=w` and `t=u(1)` produces the whole
group. The returned group orders agree with the standard formula at both
levels.

Next it enumerates the subgroups

```text
H=<r>,   N=<r,x>,   P=<r,t>,   A=<a>,   B=<b>.
```

The resulting orders are those displayed in (MBH1). In particular it sees
the corrected central-sign phenomenon directly:

```text
|H|=2n,   |N|=4n,   |P|=2mn
```

for `m=4^n-1` at `n=2,3`.

The vertex and edge coordinates are the left cosets `P\G_m` and `N\G_m`.
For every left `A`-coset represented by `g`, the program inserts the
binary row with ones at

```text
Ng,   Nag,   Na^2g.
```

It does the same with `b` for every left `B`-coset. Distinct face cosets
are retained even when the nonglobal central sign makes their three edge
coordinates identical. Hence the row counts and the parity matrix are
exactly those of the diagonal code, not a quotient which silently deletes
duplicate checks.

Python integers store the rows as bit vectors. The elimination routine
repeatedly cancels the largest occupied column against the unique stored
pivot and stores a row only when it creates a new pivot. This is ordinary
exact Gaussian elimination over `F_2`; it uses no floating point or random
choice. It returns ranks `157` and `8785`.

The edge graph is connected because `P` contains `t` and
`<P,x>=<t,x>=G_m`. Therefore the vertex-coboundary space has dimension
`V-1`. Since cellular coboundaries are contained in the kernel of the
cellular curl,

```text
dim Z^1=E-rank(delta_1)>=V-1.
```

At `m=15`, elimination gives `180-157=23=24-1`; at `m=63`, it gives
`9072-8785=287=288-1`. Equality proves (MBH2)-(MBH3).

Finally consider the Smith normal form of an oriented integral matrix
`D_Z`. The number of its nonzero invariant factors is its rational rank.
After reduction modulo two, exactly the odd invariant factors remain
nonzero. Thus the rational rank minus the binary rank is the number of
even nonzero invariant factors. When the rational kernel is the
`V-1`-dimensional coboundary space, subtracting that same space from the
binary kernel proves (MBH4). This explains why characteristic-zero
rigidity and the mod-two assertion are logically different.
