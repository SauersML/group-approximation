---
rg: 2
id: carrier-local-holonomy-rank-mf-proof
kind: route
title: Normalize trace in the surviving carrier and separate its holonomy polytope
target: holonomy-rank-gap-is-a-carrier-local-mf-certificate
requires:
  - finite-packet-holonomy-cuts-the-multiplicity-simplex
  - finite-packet-rank-polytope-is-complete
  - opnorm-packet-exactification-is-dimension-free
artifacts:
  - research/artifacts/property-t-free-rank-polytope-holonomy-integration-2026-08-25.md
---

Assume a corona representation keeps `z` nontrivial and apply the stated
authentication property.  Clause 2 exactifies the fixed semisimple packet,
changing its block projections by `o(1)` in operator norm.  For an
authenticated transport `U` from sector `alpha` to `sigma(alpha)`, clauses 3
and 5 then give

```text
||U e_alpha U^* - e_(sigma(alpha))||_op=o(1).
```

For large coordinates this norm is less than one.  Two finite-dimensional
projections at distance less than one have equal rank.  Thus every transport
preserves the exact sector ranks, and composing around cycles makes the
dimension-weighted multiplicity state exactly `H`-invariant.  The exactified
target rank vector therefore lies in `P=L(Delta^H)`.  The same operator-norm
rank rigidity, together with clause 4, says that the source ranks converge to
`r`; selector exactification changes their trace reads only by `o(1)`.

Because `P_n` is nonzero, its corner has normalized trace

```text
tau_(P_n)(X)=Tr(X)/rank(P_n).
```

For every corner matrix, Cauchy--Schwarz gives
`||X||_(2,P_n)<=||X||_op`; no factor involving
`rank(P_n)/d_n` occurs.  The rank-polytope theorem therefore gives, up to the
preceding `o(1)` source and selector perturbations,

```text
max_i delta_(i,n)
 >= 2 dist_infinity(r,P)-o(1)>0
```

in the normalized corner Hilbert--Schmidt norm.  Clause 5 says every one of
the corresponding operator defects tends to zero, contradicting this fixed
lower bound.  Hence every corona homomorphism kills `z`, which is `(CLM2)`.

The MF radical is an intersection of normal kernels, so it is normal.  If
`z` normally generates `G`, `(CLM2)` therefore makes the radical all of `G`.
