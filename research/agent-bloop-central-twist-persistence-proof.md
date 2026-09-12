---
rg: 2
id: agent-bloop-central-twist-persistence-proof
kind: route
title: Separate a virtually split central sign in one finite quotient
target: agent-bloop-central-twist-must-be-persistent
requires:
  - good-groups-have-no-persistent-finite-cohomology
---

Let `Lambda`, `J`, `H`, and `alpha` be as in the target claim.  If
`res^H_(H_0)(alpha)=0` for some finite-index `H_0<=H`, the extension splits
over `H_0`.  The image `K` of a section has finite index in `Lambda` and
meets `<J>` trivially.  Its normal core

```text
N=intersection_(lambda in Lambda) lambda K lambda^(-1)
```

also has finite index.  Centrality of `<J>` gives

```text
<J> intersect lambda K lambda^(-1)
 =lambda(<J> intersect K)lambda^(-1)=1
```

for every `lambda`, hence `N intersect <J>=1`.  The finite quotient
`F=Lambda/N` therefore sees `J`.

Write `q_F=(1-J_F)/2` for its nonzero negative central projection.  The
finite-support corner map descends to

```text
B -> q_F C[F]q_F.
```

The normalized restriction of the canonical trace of `C[F]` is a
finite-dimensional tracial state on the target corner.  Its pullback is a
Connes-embeddable trace on `B`, a contradiction.  Thus `alpha` survives on
every finite-index subgroup.

If `H` were good, the required claim
`good-groups-have-no-persistent-finite-cohomology` would force this
finite-coefficient degree-two class to vanish after finite-index
restriction.  Hence `H` is not good.  The hyperbolic virtually special,
finite, virtually free, and cubulated-hyperbolic exclusions follow exactly
as recorded in the target claim.  End proof.
