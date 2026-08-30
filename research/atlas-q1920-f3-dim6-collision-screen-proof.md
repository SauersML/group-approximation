---
rg: 2
id: atlas-q1920-f3-dim6-collision-screen-proof
kind: route
title: Exhaust the six-dimensional radial centralizers and collision words
target: atlas-q1920-six-dimensional-f3-seam-is-signal-free
requires:
  - atlas-q1920-clifford-four-dimensional-shortcut-fails
artifacts:
  - experiments/atlas_a4_q1920_f3_dim6_seam_search.g
  - experiments/verify_atlas_q1920_finite_certificates.py
  - research/artifacts/atlas-a4-q1920-f3-dim6-seam.json
---

For each of the two markings, the verifier selects every faithful
six-dimensional irreducible module having nonzero first-radial fixed space.
It computes the pointwise radial centralizer in `GL6(3)` exactly; both
centralizers have order

```text
3888 = 2^4 * 3^5.
```

Enumerating all 3,888 elements leaves 110 whose square is one, including the
identity.  Direct finite-field multiplication first imposes `(ct)^3=1` and
then

```text
t c s c t^-1 c s t c = 1.
```

For each marking exactly one element survives each stage, and that element
is the identity.  As a separate last test, the program intersects its
minus-one eigenspace with the common fixed space of `r,u`; the intersection
has dimension zero.  Hence no nonzero fixed vector representing `z` can be
inverted, and the six-dimensional signal is excluded.  The checksum audit
confirms the common profile, including the identity edge case, for both
markings.
