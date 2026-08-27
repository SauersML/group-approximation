---
rg: 2
id: fixed-packet-julia-calculus-is-tracially-functorial
kind: claim
title: Fixed-packet Julia calculus cannot manufacture the matrix-only heat return
distinct_from:
  universal-block-return-violates-the-regular-firewall: that rules out fixed group-algebra products with unequal projection traces; this covers continuous Julia/graph functional calculus after finite-packet exactification.
  packet-natural-selectors-cannot-extract-one-bounded-copy: that rules out selecting one multiplicity copy; this shows that keeping the whole multiplicity algebra makes the proposed dilation valid in the regular finite von Neumann algebra as well.
  julia-dilation-packages-heat-as-one-cross-gram-moment: that positively packages the amplitude target; this proves the package alone cannot return the marked source.
---

Fix a finite packet group `F` and one irreducible type `rho` of dimension
`r`.  In every exact representation its selected corner has the form

```text
C^r tensor M,                                          (FJC1)
```

where `M` is an arbitrary multiplicity space.  Replacing a matrix
multiplicity algebra by an arbitrary finite tracial von Neumann algebra `N`
turns the packet corner into

```text
M_r(C) tensor N.                                       (FJC2)
```

Every construction obtained from

- fixed packet matrix units and group-algebra coefficients,
- addition, multiplication and adjoint,
- fixed matrix amplification and compression, and
- continuous functional calculus, including Halmos/Julia defect operators

is defined verbatim in `(FJC2)` and respects the product trace.  Therefore
any exact or zero-defect identity produced by this calculus is tracially
functorial.  It cannot yield, for a nonzero regular carrier `P`,

```text
YX=P,
XY=E Q_(B_t) E                                         (FJC3)
```

for arbitrarily large `t`: cyclicity and `(JHG3)` would force
`tau(P)=0` in the regular representation.

Consequently a selected finite packet does not make the Julia dilation
matrix-only.  Its arbitrary multiplicity unitary is not the obstruction --
the whole multiplicity algebra survives, and Julia calculus is natural on
that algebra.  The graph projection has constant half-rank; determinant or
parity of the fixed `2 by 2` dilation supplies at most a bounded-dimensional
defect and has no normalized-HS density.

The minimum additional datum is one operation unavailable in an arbitrary
finite von Neumann multiplicity algebra: an integer-rank/conductor selector,
an authenticated finite-coordinate spectral cutoff, or an equivalent
nonfunctorial common-carrier moment which compares the fixed mark to
`tau(EQ_(B_t))`.  Without that datum, 2 by 2 and 3 by 3 word cells merely
repackage the regular firewall.
