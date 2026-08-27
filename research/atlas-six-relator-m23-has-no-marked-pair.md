---
rg: 2
id: atlas-six-relator-m23-has-no-marked-pair
kind: claim
title: The maximal A8 class in M23 has no six-relator marked pair
artifacts:
  - experiments/atlas_six_relator_m23_scan.py
  - experiments/atlas-six-relator-m23-scan.json
distinct_from:
  atlas-a4-m23-packet-double-coset-screen: that proves all thirty packet words force the identity double coset before q_19243; this tests only the five saturated words and c_19243 on every cell.
  atlas-six-relator-l5-has-no-marked-pair: that treats the preceding linear carrier with 496 cosets; this treats the sporadic maximal A8 carrier with four double cosets.
---

Let `G=M23` and let `H~=A8` be its maximal subgroup of index `506`.  There
are no injective marked maps `i_1,i_2:A8->G` satisfying all six words.

The official ATLAS degree-23 generators and maximal-`A8` straight-line
program give

```text
|G|=10200960,   |H|=|N_G(H)|=20160.
```

The four exact `H`--`H` double-coset sizes are

```text
20160, 302400, 4233600, 5644800.                    (S6M23-1)
```

The screen ranges every element of every cell, first in the inner marking
parity and then after inverse-transpose on the second alphabet.  In the
inner parity exactly one element of the identity cell reaches `c_19243`,
which rejects it.  In the graph parity no element reaches the last word.
Every nonidentity cell already has zero five-row survivors.  Both total
six-word survivor counts are zero.

Since `N_G(H)=H` and `Out(A8)=C2`, these are exactly all marked pairs up to
simultaneous conjugacy.  All evaluations are exact permutation arithmetic.
