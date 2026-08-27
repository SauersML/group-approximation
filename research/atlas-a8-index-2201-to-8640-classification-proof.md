---
rg: 2
id: atlas-a8-index-2201-to-8640-classification-proof
kind: route
title: Cross L2(449) and S4(7) by 2-rank and characteristic-seven projective degree
target: atlas-a8-index-2201-to-8640-reaches-o8p2
requires: []
artifacts:
  - experiments/atlas_a8_index_2201_to_8640_order_sieve.py
  - experiments/atlas-a8-index-2201-to-8640-order-sieve.json
---

The CFSG family order formulas, as collected in Wilson's [*The Finite Simple
Groups*](https://doi.org/10.1007/978-1-84800-988-2), give the complete list
strictly after `HS` through `O8+(2)`: the `L2(q)` rows emitted by the attached
prime-power enumeration, together with `J3`, `U3(11)`, `S4(7)`, and
`O8+(2)`.  The next parameters in every higher-rank classical and exceptional
family exceed `|O8+(2)|`; `A12` does also.  The [ATLAS J3
page](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J3/) supplies the sole
sporadic order in this interval.

Exact divisibility leaves `L2(449)`, `S4(7)`, and `O8+(2)`.  A Sylow
2-subgroup of `L2(449)` is dihedral, so its elementary-abelian 2-rank is two,
excluding `C2^4<A8`.  The characteristic-seven projective-degree argument in
`(SIO2)` excludes `S4(7)`.  Finally the [ATLAS O8+(2)
page](https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/O8p2/) gives order
`174182400=8640*20160`, proving the endpoint.

