---
rg: 2
id: baumslag-address-geometric-stationary-profile
kind: claim
title: The finitely compressed Baumslag prefix still has exact geometric stationary models
distinct_from:
  finite-packet-flow-keeps-payload-orientation-balanced: That installs the regular stationary vector in an arbitrary finite packet diagram; this gives explicit unbounded finite-field quotients of the Baumslag address host and computes the first-hit prefix masses.
  baumslag-binomial-prefix-centralizer: That proves all earlier-lamp commutators from two relators; this shows those relators do not prevent geometric loss of the payload carrier.
  first-hit-carrier-contraction-ladder: That derives collapse assuming persistent carriers; this supplies exact models in which summability holds but persistence fails by the factor `2^(-n)`.
---

**ESTABLISHED STATIONARY FIREWALL.**  The finite prefix compressor does not
make a payload carrier persist.  For every `m>=2`, choose an element `alpha`
of degree `m` over `F_2`.  In the finite affine group on the additive group
of `F_(2^m)`, let the two commuting actor letters act by multiplication by
`alpha` and `1+alpha`, and let `a` be translation by `1`.  With the choice of
actor convention matching `x^y=y^(-1)xy`, this gives a finite quotient of

```text
Lambda_2=<a,b,c | a^2=1,[b,c]=1,[a^b,a]=1,a^c=a^b a>. (BSP1)
```

Both multipliers are invertible.  The first `m` lamp words `B_n` have
translation vectors `1,alpha^(-1),...,alpha^(-(m-1))` up to reversing the
actor convention.  They are linearly independent because `alpha^(-1)` also
has degree `m`.  Hence, in the regular representation of the finite
translation subgroup,

```text
C_n=product_(k<n)(1+B_k)/2,
X_n=C_n(1-B_n)/2
```

obey, for `0<=n<m`,

```text
tau(C_n)=2^(-n),              tau(X_n)=2^(-(n+1)).     (BSP2)
```

The extra prefix-centralizer letter from
`baumslag-binomial-prefix-centralizer` may
be represented trivially, so `(BBC2)--(BBC4)` are exact in these models.
More generally, any fixed finite list of regular-balanced packet/HNN rows
over the first `N<m` lamps extends after taking a common regular multiple:
isomorphic source and target subgroup restrictions have the same regular
multiplicity.  Thus the finite address and transport errors can all vanish
while `(BSP2)` remains exact.

Tensor this address model with a scalar structural shared-BCS assignment.
For the fixed non-CE BCS such an assignment violates at least one forbidden
atom (otherwise it would itself be a perfect matrix model).  The forbidden
payload therefore has positive mass, but an independently addressed carrier
has

```text
q_n=tau(Q C_n)=2^(-n)tau(Q),                           (BSP3)
```

and its first-hit charge is only of the same geometric order.  First-hit
summability `(FHC3)` is satisfied, but persistence `(FHC1)` would require

```text
Delta_n >= (1-2^(-n))tau(Q).                          (BSP4)
```

This is an exact zero-presentation-energy countermodel to obtaining FHC1
from the Baumslag address relations, their compressed prefix centralizer,
and regular-balanced local HNN atoms alone.

The scope is precise.  It does not rule out a new payload-dependent row that
excludes these finite-field multiplicity profiles on the actual canonical
reached hull.  It proves that infinite addressing and polynomial prefix
authentication do not themselves do so.  A successful tail still needs the
same supercritical active-child/proper-corner incidence isolated by the BTB
compiler; otherwise the regular compensation simply decays geometrically
down the prefix.

`one-dimensional-address-rules-have-periodic-models` gives the parallel
structural reason for finite-state lamplighter/HNN tables: every nonempty
one-dimensional finite-type active fiber has an exact periodic cyclic model.
The present finite-field construction is the affine Baumslag analogue beyond
a fixed finite alphabet.  Together they show that changing the address host
from a local shift table to the compressed binomial prefix does not create
nonstationary payload ownership; both retain zero-defect finite active models.

DERIVATION
baumslag-finite-field-prefix-profile-proof
