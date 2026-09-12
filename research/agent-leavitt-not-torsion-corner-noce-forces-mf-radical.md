---
rg: 2
id: agent-leavitt-not-torsion-corner-noce-forces-mf-radical
kind: claim
title: A no-CE algebra in one torsion spectral corner forces that torsion mark into the MF radical
distinct_from:
  nonhyperlinear-normal-augmentation-corner-kills-mf: that uses the full augmentation complement of a finite normal subgroup and concludes that the whole subgroup dies; this needs neither normality nor centrality and authenticates one specified finite-order element through its complete nontrivial spectral projection.
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that uses the canonical group trace and concludes that the ambient group is nonhyperlinear; this cuts every norm-matrix-corona representation by the image of the prescribed torsion projection and concludes radical membership of the marked element.
artifacts:
  - research/agent-leavitt-not-torsion-corner-noce-radical-proof.md
---

**ESTABLISHED.**  Let `B` be a unital star algebra with no Connes-embeddable
tracial state, let `G` be a countable group, and let `z in G` have finite
order `m`.  Put

```text
e_z=(1/m)sum_(j=0)^(m-1) z^j,          q_z=1-e_z in C[G].    (TCN1)
```

If there is a unital star homomorphism

```text
Phi:B -> q_z C[G] q_z,                 Phi(1_B)=q_z,          (TCN2)
```

then

```text
z in Rad_MF(G).                                                (TCN3)
```

No normality of `<z>`, centrality of `z` or `q_z`, positive ambient trace
floor, Property `(T)`, or stability input is needed.  If a norm-corona
representation sees `z`, it sees the complete nontrivial spectral projection
`q_z`.  Lift that projection, normalize each nonzero matrix corner by its own
rank, and compose `(TCN2)` with the resulting tracial matrix ultraproduct.
This would give a Connes-embeddable trace on `B`.

Finite presentation of `B` is not used in this implication.  It is relevant
only to making a proposed corner diagram a finite construction target; the
fixed BCS application has that finiteness automatically.

For an involution, `q_z=(1-z)/2`; hence the criterion applies literally to a
noncentral marked root.  If `z` normally generates `G`, `(TCN3)` implies
`Rad_MF(G)=G`.
