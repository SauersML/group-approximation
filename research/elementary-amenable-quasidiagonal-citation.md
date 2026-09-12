---
rg: 2
id: elementary-amenable-quasidiagonal-citation
kind: route
title: Literature import of Ozawa-Rordam-Sato
target: elementary-amenable-groups-are-quasidiagonal
requires: []
artifacts:
  - research/artifacts/property-t-free-counterexamples-2026-09-07.md
---

## Source

N. Ozawa, M. Rordam, Y. Sato, *Elementary amenable groups are quasidiagonal*,
Geometric and Functional Analysis **25** (2015), 307-316.
Author copy: `https://web.math.ku.dk/~rordam/manus/ElementaryAmenable.pdf`.

The theorem is that `C*(G)` is quasidiagonal for every countable elementary
amenable `G`.

## The step this repository takes on top of it

Quasidiagonality of a unital separable C-star algebra gives a unital
completely positive contractive map into `prod_n M_(d_n) / directsum_n M_(d_n)`
which is a faithful `*`-homomorphism, so `C*(G)` is MF, so the canonical
unitaries give an injective group homomorphism

```text
G --> U( prod_n M_(d_n) / directsum_n M_(d_n) ).
```

That is the repository's definition of an MF group.  No amenability argument
of our own is used and none is claimed.
