---
rg: 2
id: nonhyperlinear-from-wedderburn-transport-cost
kind: route
title: A positive-dual Fourier transport cost rules out regular-A8 atlas microstates
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - unitary-block-energy-transport
  - atlas-wedderburn-soft-transport-certificate
---

Assume `Q=L_(F_2)(1,2)^x` were hyperlinear.  By
`leavitt-regular-atlas-hyperlinearity-criterion` there would be external
multiplicities `k_n` and relative chart unitaries `U_n` with canonical packet
defect `delta_n -> 0`.

Apply `atlas-wedderburn-soft-transport-certificate` to each `U_n`.  It returns
costs and dual potentials whose dual value is at least the fixed `gamma>0` but
whose actual block-energy cost is at most

```text
C delta_n^c -> 0.                                     (NT1)
```

On the other hand `unitary-block-energy-transport` says the squared Fourier
block energies of `U_n` are an exact transportation plan with the fixed regular
marginals.  Weak transport duality therefore bounds the very same cost below
by `gamma` for every `n`, contradicting `(NT1)`.

Hence the regular-A8 feasibility criterion fails and `Q` is nonhyperlinear.
The soft-cost formulation is useful because it can search weighted quadratic
packet energies before choosing a hard support cut.  By
`soft-transport-thresholds-to-hall-subsequence`, however, a successful
asymptotic soft certificate on this fixed Fourier alphabet automatically
contains a hard Hall-deficient subsequence; it is an optimization relaxation,
not a weaker endpoint theorem.
