---
rg: 2
id: near-regular-finite-character-fixes-plancherel-types
kind: claim
title: A near-regular finite-group character fixes every irreducible at Plancherel density
distinct_from:
  plancherel-restriction-coupling: that gives the exact coupling of regular representations down subgroup chains; this is a quantitative estimate for one nearly regular finite-dimensional character.
  regular-finite-controlled-phase-has-half-wrong-mass: that computes one abelian phase split in the exact regular representation; this controls every irreducible multiplicity simultaneously.
---

Let `H` be finite and let `rho:H->U(d)` be exact. Suppose its normalized
character `t(h)=Tr(rho(h))/d` satisfies

```text
|t(h)|<=eta                    for every h!=1.          (NRC1)
```

For `pi in Irr(H)`, let `m_pi` be its multiplicity in `rho` and
`d_pi=dim(pi)`. Then its normalized Hilbert-space mass obeys

```text
|d_pi m_pi/d-d_pi^2/|H||
 <= d_pi^2 (|H|-1) eta/|H|.                           (NRC2)
```

In particular, along exact finite-group representations whose normalized
characters converge to the regular character, every fixed `pi`-isotypic
carrier converges to its positive Plancherel density `d_pi^2/|H|`.

After fixed-table flexible exactification, the same conclusion holds with an
additional error controlled by the exactification loss. Thus a regular-trace
hyperlinear microstate cannot dilute a chosen irreducible of an embedded fixed
finite group to zero mass.
