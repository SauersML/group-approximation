---
rg: 2
id: infinite-kazhdan-subgroup-of-nv-from-hyperbolic-embeddings
kind: route
title: If every hyperbolic group embeds in some nV, some nV contains an infinite Kazhdan group
target: some-brin-thompson-group-has-an-infinite-kazhdan-subgroup
requires:
  - every-hyperbolic-group-embeds-in-some-brin-thompson-group
  - torsion-free-hyperbolic-kazhdan-partner-exists
---

1. By `torsion-free-hyperbolic-kazhdan-partner-exists` there is an infinite
   word-hyperbolic group `H` with property (T).
2. By `every-hyperbolic-group-embeds-in-some-brin-thompson-group`, `H` embeds in
   nV for some n.
3. The image is an infinite subgroup of nV with property (T). By Farley's
   theorem (`thompson-v-has-haagerup-property`) this forces n ≥ 2. The route
   does not need that fact, so it is not listed in requires.

This links Zaremsky Problems 2.19(a) and 2.7: an affirmative answer to 2.19(a)
answers the Haagerup half of 2.7 negatively for large n.
