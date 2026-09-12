---
rg: 2
id: finite-group-multiplicity-mismatch-pays-hs-energy
kind: claim
title: Extensive finite-group multiplicity mismatch forces constant normalized-HS intertwining energy
distinct_from:
  finite-group-intertwiner-laplacian-gap: that supplies a uniform spectral gap off the exact intertwiner space; this computes how far every unitary must lie from that space when the two representation multiplicity profiles differ.
  finite-group-intertwiner-shrinkage-formula: that computes the largest shrunk-subspace deficiency of the exact intertwiner space; this turns the same weighted multiplicity defect into a lower bound for every unitary transport.
  fixed-holonomy-on-overlap-pays-relator-energy: that charges a prescribed nontrivial finite-factor holonomy on a named corner; this charges arbitrary isotypic multiplicity mismatch without choosing a holonomy element.
---

Fix a finite group `H`, a finite generating set `S`, and the constant
`kappa(H,S)>0` from `finite-group-intertwiner-laplacian-gap`.  Let `rho` and
`sigma` be exact unitary representations of `H` on Hilbert spaces of the same
dimension `d`, with isotypic decompositions

```text
rho   = directSum_lambda S_lambda^(direct sum m_lambda),
sigma = directSum_lambda S_lambda^(direct sum n_lambda),
d_lambda = dim S_lambda.
```

Put

```text
L = sum_lambda d_lambda |m_lambda-n_lambda|.
```

Then every unitary `U` between the two representation spaces satisfies

```text
sum_(s in S) ||rho(s)U-U sigma(s)||_(2,d)^2
  >= (kappa(H,S)/2) (L/d).                              (FGMP1)
```

Here `||.||_(2,d)` is normalized Hilbert--Schmidt norm.  In particular an
`Omega(d)` weighted multiplicity discrepancy costs `Omega(1)` normalized-HS
energy, with a constant depending only on the fixed finite packet and its
chosen generators.

The factor `1/2` is the exact conversion from weighted `L1` mismatch to
unmatched Hilbert dimension when the total dimensions agree:

```text
d - sum_lambda d_lambda min(m_lambda,n_lambda) = L/2.  (FGMP2)
```

This is the payment theorem needed by any Schur--Clifford return relation once
the rank jump has been converted into a mismatch between two exact
representations of one fixed packet group.  It does not itself construct that
return or prove that the mismatch is extensive.
