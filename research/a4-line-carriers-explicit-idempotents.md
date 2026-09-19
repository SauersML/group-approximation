---
rg: 2
id: a4-line-carriers-explicit-idempotents
kind: claim
title: The three regular A4 line carriers are explicit central idempotents
---

For each character `chi` of the order-three subgroup `<a>` in
`A4=<a,b | a^3=b^2=(ba)^3=1>`, let `xi_chi` be the unique one-dimensional
character of `A4` extending `chi`; it has `xi_chi(b)=1`.  In any unitary
representation `rho` of `A4` define

```text
E_chi = (1/12) sum_(g in A4) conjugate(xi_chi(g)) rho(g).
```

Then `E_chi` is the central projection onto the `xi_chi`-isotypic summand.  In
a multiple of the regular representation it equals the top spectral carrier
from `a4-regular-line-sector-spectral-split`:

```text
E_chi = 1_[2/3,1](P_chi Q_+ P_chi),
```

where `P_chi` is the `chi` spectral projection of `rho(a)` and
`Q_+=(1+rho(b))/2`.

Thus each line carrier is a fixed finite linear combination of the twelve A4
representation matrices, rather than an object requiring dimension-dependent
functional calculus.  In every regular amplification its normalized trace is
`1/12`.

If two exact A4 vertex representations are `eps`-close on the fixed generators
`a,b`, their corresponding `E_chi` projections are `O(eps)`-close by finite
word telescoping, with a constant independent of external multiplicity.