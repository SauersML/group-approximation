---
rg: 2
id: stw84-balanced-mass-obstruction-for-coordinate-colours-proof
kind: route
title: Split the largest Fourier colour into two balanced diagonal masses
target: stw84-bounded-coordinate-colour-gap
requires:
  - stw84-weighted-fourier-cutdown-and-row-gap
artifacts:
  - research/artifacts/stw84-coordinate-colouring-firewall-2026-08-30.md
---

Choose a colour `c` of maximal cardinality `m=|S_c|`.  Split `S_c` into
disjoint subsets `P,Q` with

```text
|P|=floor(m/2),       |Q|=ceil(m/2),
```

and denote their characteristic functions in `C^(S_c)` by `p,q`.  They are
orthogonal positive contractions.  Hence order zero gives

```text
Psi_c(p)Psi_c(q)=0.                                    (CCF4)
```

On the other hand,

```text
Lambda_(h,n)(p)=(|P|/n)h,
Lambda_(h,n)(q)=(|Q|/n)h,
```

and therefore

```text
||Lambda(p)Lambda(q)||=|P||Q|/n^2,                    (CCF5)
```

because `||h^2||=1`.  Put
`epsilon=||Lambda_(h,n)-Psi||`.  Since `p,q` live entirely in the selected
colour, `Psi(p)=Psi_c(p)` and `Psi(q)=Psi_c(q)`.  Using `(CCF4)`,

```text
Lambda(p)Lambda(q)
 =[Lambda(p)-Psi(p)]Lambda(q)
  +Psi(p)[Lambda(q)-Psi(q)].                           (CCF6)
```

Both factors not measured by `epsilon` are contractions.  Equations
`(CCF5)--(CCF6)` give

```text
epsilon>=floor(m/2)ceil(m/2)/(2n^2),
```

which is `(CCF3)`.

If `n>=2d`, the pigeonhole principle gives `m>=n/d>=2`.  For every integer
`m>=2`,

```text
floor(m/2)ceil(m/2)>=m^2/8.
```

Substitution in `(CCF3)` yields `(CCF2)`.

For the Fourier-row consequence, the diagonal matrix unit `e_ii` satisfies

```text
Theta_(h,n)(e_ii)=h/n,
```

independently of `i`, `U`, and all covariance estimates.  Thus restriction
to the scalar diagonal is `(CCF1)`, and the preceding proof applies without
change.  Restriction of an order-zero map to any coordinate summand remains
order zero, so coefficient matrix amplifications do not evade the bound.

The argument assumes that each diagonal coordinate is assigned to one of a
bounded number of colours.  A general nuclear-dimension factorization can
send one input element to several finite-dimensional summands and need not
preserve a coordinate diagonal.  Accordingly, the result is a firewall for
the natural Fourier-coordinate schemes, not a lower bound on the nuclear
dimension of the crossed product.
