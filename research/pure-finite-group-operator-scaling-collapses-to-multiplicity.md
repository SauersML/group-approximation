---
rg: 2
id: pure-finite-group-operator-scaling-collapses-to-multiplicity
kind: claim
title: Vanishing-cutoff operator scaling for a fixed finite group sees only multiplicity imbalance
distinct_from:
  atlas-spectral-shrunk-intertwiner-certificate: that open atlas target may use mixed chart relators and microstate-dependent singular directions; this theorem only classifies the tempting special case where its Laplacian is a pure fixed-finite-group intertwiner Laplacian.
---

Fix a finite group `H` and generators `S`.  Let `rho_n,sigma_n` be pairs of
finite-dimensional unitary `H`-representations on equal `d_n`-dimensional
spaces, let `L_n` be their standard intertwiner Laplacian, and let `a_n->0`.
Write the isotypic multiplicities as `m_(n,lambda),n_(n,lambda)`.

For all sufficiently large `n`, the spectral space `K_(a_n)` satisfies

```text
K_(a_n) = Hom_H(sigma_n,rho_n),                         (PFG1)
```

and its exact maximal normalized shrinkage is

```text
(1/d_n) max_X (dim X-dim K_(a_n)(X))
 = (1/(2d_n)) sum_lambda
   d_lambda |m_(n,lambda)-n_(n,lambda)|.                (PFG2)
```

Consequently a uniform `gamma d_n` shrunk-space certificate in this regime is
**equivalent** to a uniform weighted isotypic multiplicity mismatch.  If the
normalized weighted `L1` mismatch tends to zero, every shrunk deficiency is
`o(d_n)`.

For the atlas operator-scaling program this is a useful boundary: a cutoff
`tending to zero around a Laplacian made only from one fixed exactified finite
chart group cannot uncover a hidden non-coordinate shrunk space.  Any genuine
advantage over the existing Wedderburn/Hall formulations must come from at
least one of:

- a linear-size finite multiplicity mismatch itself;
- mixed atlas relations which do not reduce to one fixed finite-group
  intertwining problem; or
- a cutoff deliberately retaining positive spectral modes rather than
  eventually falling below the fixed finite-group gap.

This does not obstruct `atlas-spectral-shrunk-intertwiner-certificate`; it
removes one overly broad implementation class and says exactly where its new
information has to enter.
