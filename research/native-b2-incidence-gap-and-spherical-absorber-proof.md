---
rg: 2
id: native-b2-incidence-gap-and-spherical-absorber-proof
kind: route
title: Compute the B2 incidence coefficient and compress every native map to constants
target: native-km-coset-coefficients-retain-spherical-pauli-absorber
requires:
  - simple-kazhdan-kac-moody-lattices-exist
  - three-reynolds-plus-kernel-energy-has-vanishing-gap
---

The rank-two regular chart is the left action on `ell^2(P_ij)`.  Splitting
first into right `P_0` cosets and then into right `P_i` cosets gives exactly
the fiber-sum operator `(NKC2)`; hence these are the unreduced restriction
coefficients, not a character-free surrogate.  A constant function has the
same sum on every fiber, proving invariance of the spherical line.  Every
composition of the `R_(ij,i)`, their adjoints, and group-equivariant label
maps therefore acts scalarly on that line.  Tensoring a regular chart by
`C^m` makes its multiplicity endomorphism algebra `M_m`, proving `(NKC3)`
and its fixed density.

For completeness, the `B_2` coefficient can be diagonalized without a
character-table lookup.  In a generalized quadrangle of order `(q,q)`, its
point collinearity graph has parameters

```text
v=(q+1)(q^2+1),  k=q(q+1),  lambda=q-1,  mu=q+1.       (NBP1)
```

If `A_col` is its adjacency matrix and `N_13` the point-line incidence
matrix, then

```text
N_13 N_13^*=(q+1)I+A_col.                              (NBP2)
```

The strongly regular relation

```text
A_col^2=(k-mu)I+(lambda-mu)A_col+mu J                  (NBP3)
```

shows that the nonconstant eigenvalues of `A_col` are `q-1` and `-(q+1)`;
the constant eigenvalue is `k`.  Substitution in `(NBP2)` gives `(NKC4)`.
After normalizing incidence by `q+1`, its nonconstant singular norm is
`sqrt(2q)/(q+1)`, proving `(NKC5)` and the stated angle gap.

Now restrict the complete native coefficient system to the tensor product
of all spherical label lines with one common multiplicity algebra.  Every
finite-label coefficient becomes a scalar, so the only nontrivial operators
left are the multiplicity gauges and their cycle words.  The coset graph
description of the free kernel gives one basis cycle for each chord outside
a spanning tree.  Its multiplicity holonomies are independent: gauge the
tree and all but one chord by `I`, and put `Y_t=AD_tAD_t` on the remaining
chord.  This changes no vertex representation or label coefficient.  The
actual free-basis kernel coefficients are then `I,...,I,Y_t`.

On `V=span_R{B,C}`, conjugation by `Y_t` is rotation through `-8t`, so the
only nonzero kernel square is `(NKC7)`.  Its positive eigenvectors are
orthogonal to the exact fixed space.  This proves `(NKC8)`.  Amplification
preserves the label density and the normalized Hilbert--Schmidt calculation.
