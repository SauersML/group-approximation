---
rg: 2
id: one-sided-raw-qutrit-head-proof
kind: route
title: Separate one-sided head words by finite nilpotent shifts
target: one-sided-raw-qutrit-head-bridges-are-residually-finite
requires:
  - qutrit-head-only-overlap-envelope-is-finite
  - one-balanced-actor-qutrit-bridge-is-jacobson-core
  - property-t-free-leavitt-via-jacobson-head-root
---

In `J`, the identities `Q^2=Q` and `QS=0` reduce every word in
`S,Q` to a linear combination of

```text
S^k,             S^i Q,                   k,i>=0.       (ORQ3)
```

These normal words are linearly independent.  Indeed
`S^iQ=S^i-S^(i+1)T`, and the standard Jacobson normal forms
`S^pT^q` are linearly independent.  The terms with `q=1` first force
all coefficients of `S^iQ` to vanish, after which the pure `S^k`
coefficients vanish.  This proves the asserted embedding of `A_+`.

For `N>=0`, let `V_N` have basis `e_0,...,e_N`.  Define

```text
S_N e_j=e_(j+1) for j<N,       S_N e_N=0,
Q_N e_0=e_0,                   Q_N e_j=0 for j>0.       (ORQ4)
```

Then `Q_N^2=Q_N` and `Q_NS_N=0`, so `(ORQ4)` defines a unital
homomorphism

```text
rho_N^+:A_+ -> M_(N+1)(F_2).
```

Write a nonzero element as `f(S)+g(S)Q` using `(ORQ3)`.  If
`f!=0`, choose `N` larger than both degrees plus one and apply the
matrix to `e_1); the `g(S)Q` term vanishes and the distinct shifts in
`f(S)e_1` cannot cancel.  If `f=0`, apply to `e_0` with
`N>deg(g)`.  Thus some finite matrix representation detects every nonzero
element, proving that `A_+` is residually finite dimensional.

The negative algebra is symmetric at the level of the calculation.  Words
in `T,Q` reduce uniquely to combinations of

```text
T^k,             Q T^i.
```

Use the backward nilpotent shift
`T_Ne_j=e_(j-1)` for `j>0), `T_Ne_0=0), and the same projection
`Q_N` onto `e_0`.  Then `T_NQ_N=0`.  Acting first on a sufficiently
far basis vector detects the pure polynomial part; acting on the appropriate
`e_i` detects a nonzero `QT^i` coefficient.  Hence `A_-` is also
residually finite dimensional.

It remains to identify the groups.  Scalar permutation conjugacy moves
`x_12(S)`, `x_12(T)`, and `x_12(Q)` to every root position.
Root additivity and

```text
[x_ik(r),x_kj(s)]=x_ij(rs)
```

then generate every coefficient in the relevant algebra.  This proves both
equalities in `(ORQ2)`.

Finally, a matrix group over a residually finite-dimensional
`F_2`-algebra is residually finite.  If a matrix differs from the identity,
choose a nonzero entry of the difference and a finite-dimensional algebra
representation detecting it.  Entrywise application maps the matrix
nontrivially into the unit group of a finite matrix algebra.  Therefore both
`H_+` and `H_-` are residually finite.
