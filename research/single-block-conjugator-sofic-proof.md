---
rg: 2
id: single-block-conjugator-sofic-proof
kind: route
title: Peel the least of three indices using only cyclic edge groups
target: single-block-conjugator-one-relator-groups-are-sofic
requires: []
artifacts:
  - research/artifacts/triangular-bs-chain-proof-2026-09-07.md
  - research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md
  - experiments/one_relator_cyclic_peeling_check.py
  - research/artifacts/one-relator-cyclic-peeling-replay-2026-09-07.json
---

Put `d=p+q`. The identity `b^p a^s b^q=b^d a_q^s` rewrites the kernel
relators using `x=a_i`, `y=a_(i+d)`, `z=a_(i+q)` as

    (z^(-s) y z^s)^(-1) x^l (z^(-s) y z^s) = x^k.

When `0,d,q` are distinct, process any finite set of relators in decreasing
order of their least generator index. That least generator is new; the
other two already have infinite order. The artifact gives explicit
constructions according to its role:

* new `x`: amalgamate a Baumslag-Solitar block along its stable letter;
* new `y`: take a cyclic-edge HNN extension along powers of `z^s x z^(-s)`;
* new `z`: attach a Baumslag-Solitar block along `x`, adjoin an HNN letter
  conjugating `y` to its stable letter, then adjoin an `s`-th root by a
  cyclic amalgam.

Every edge map is checked injective, old groups embed, and the newly
adjoined generator has infinite order. Eliminating auxiliary generators
gives exactly the displayed relator in each case. Colliding indices and
`s=0` reduce to the separately constructed two-generator blocks in the
artifact. The finite-table direct-limit argument then gives a sofic
kernel; extension by `Z` gives the stated group.
