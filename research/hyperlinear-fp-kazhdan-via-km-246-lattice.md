---
rg: 2
id: hyperlinear-fp-kazhdan-via-km-246-lattice
kind: route
title: A sofic (2,4,6) Kac-Moody lattice is a finitely presented simple sofic Kazhdan group
target: hyperlinear-fp-infinite-simple-kazhdan-group
requires: [km-246-lattice-is-sofic, km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4, sofic-implies-hyperlinear]
---

Let `q >= 4` be a prime power for which `km-246-lattice-is-sofic` holds, and `S_q = Lambda_q/Z`.
- By `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`, `S_q` is infinite, finitely
  presented, simple and Kazhdan.
- It is sofic by hypothesis, which is the preferred form of the target.
- `sofic-implies-hyperlinear` gives the hyperlinear form.
