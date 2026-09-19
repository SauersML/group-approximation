---
rg: 2
id: stw99-lxvi-unbounded-stability-index-proof
kind: route
title: Follow minimal CAR projections down the finite corner
target: stw99-lxvi-car-corner-forces-unbounded-stability-indices
requires:
  - stw99-lxvi-car-corner-iff-coherent-dyadic-v-chain
---

At the standard `M_(2^n)` stage of the unital CAR copy in `pBp`, choose a
minimal projection `p_n`, compatibly so that `p_(n+1)<=p_n`.  The matrix units
give

```text
[p]=2^n[p_n] in V(B).
```

In particular, the unit of `M_(2^n)(p_nBp_n)` is Murray--von Neumann
equivalent to `p`, and is therefore finite.  If the unit of a smaller
amplification `M_m(p_nBp_n)` were infinite, adjoining an identity summand
would make the unit of every larger amplification, including size `2^n`,
infinite.  Hence all sizes `m<=2^n` remain finite.  Each `p_n` itself is a
subprojection of the finite projection `p`, so it is finite as well.

On the other hand, `p_n` is nonzero and therefore full in the simple algebra
`B`.  Pulling an ambient infinite projection into a finite matrix over
`p_nBp_n`, exactly as in
`stw99-lxvi-full-finite-corner-is-nonstable-proof`, shows that this corner is
not stably finite.  Its first infinite amplification `mu(p_n)` therefore
exists and satisfies `mu(p_n)>2^n`.

The final assertion follows immediately: a uniform upper bound on all these
indices is incompatible with the displayed exponential lower bounds.
