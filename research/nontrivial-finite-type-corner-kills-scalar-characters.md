---
rg: 2
id: nontrivial-finite-type-corner-kills-scalar-characters
kind: claim
title: A higher-dimensional finite-group type is a positive algebraic corner annihilated by every scalar character
artifacts:
  - research/artifacts/signed-hecke-direct-trace-promotion-2026-08-20.md
distinct_from:
  augmentation-one-corner-retains-a-character: that excludes trivial-type corners; this constructs the exact augmentation-zero replacement with positive canonical trace.
---

Let `K<=Gamma` be finite and let `rho` be an irreducible representation of
`K`, of dimension `d_rho>1`, with character `chi_rho`. Its central block
projection is

```text
z_rho=(d_rho/|K|) sum_(k in K) chi_rho(k^(-1)) k.          (FTC1)
```

Then

```text
z_rho=z_rho^*=z_rho^2,
epsilon(z_rho)=0,
tau_Gamma(z_rho)=d_rho^2/|K|>0.                           (FTC2)
```

More strongly, every scalar group character `eta:Gamma->T` satisfies
`eta(z_rho)=0`, because `eta|_K` is one dimensional and is orthogonal to
`rho`. Thus `z_rho C[Gamma]z_rho` has a positive canonical corner trace while
all scalar characters of the ambient group annihilate its unit.
