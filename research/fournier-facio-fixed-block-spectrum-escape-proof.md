---
rg: 2
id: fournier-facio-fixed-block-spectrum-escape-proof
kind: route
title: Combine nonsofic fixed blocks with uniform eigenphase recurrence
target: fournier-facio-fixed-block-spectrum-escapes
requires:
  - fournier-facio-monomial-near-witness-impossible
  - finite-spectrum-unitary-power-recurrence
---

Charge-null removal makes the comparison family `B_g` itself an invariant
essentially free near representation.  Its block maps induce a
`nu`-preserving near action `alpha` on `Y`; this is the same propagation
argument used in
`fournier-facio-bounded-block-near-witness-impossible`.  If every
nonidentity `g` had a null fixed-block set, `alpha` would be an essentially
free amenable near action and the Elek--Szabo characterization would make the
Fournier--Facio group sofic.  Therefore `(FFSE2)` holds for some `g!=1`.

Fix a finite `N`.  Suppose `(FFSE4)` has positive charge.  It is the union of
the `N` sets obtained by fixing the exponent, so finite additivity gives an
`n`, `1<=n<=N`, for which

```text
||U_(g,y)^n-I||_op<1/4                                (FFSP1)
```

on a positive-charge set of fixed blocks.  Repeated near multiplication
gives

```text
B_(g^n) = B_g^n
```

in the charged column seminorm.  Remove the null exceptional columns at
tolerance `1/4`.  For every remaining basis vector `delta_x` in the
positive block sector, `(FFSP1)` gives

```text
|<B_g^n delta_x,delta_x>|>3/4,
|<B_(g^n) delta_x,delta_x>|>1/2.                       (FFSP2)
```

This contradicts essential freeness because torsion-freeness gives
`g^n!=1`.  Hence `(FFSE4)` is null.

If `U` has at most `m` distinct eigenvalues, apply
`finite-spectrum-unitary-power-recurrence` to those eigenvalues rather than
to the ambient matrix dimension.  With a fixed sufficiently large `Q`, it
produces `1<=n<=Q^m` for which `||U^n-I||_op<1/4`.  Therefore the set in
`(FFSE3)` is contained in `(FFSE4)` with `N=Q^m` and is null.
