---
rg: 2
id: tensor-factor-stopping-support-count-proof
kind: route
title: Count the linear-size stopping support of every nonabelian tensor factor
target: bounded-participation-tensor-networks-are-not-diffuse-far
requires:
  - dellm-all-dual-presentation-has-many-unique-neighbors
  - unique-neighbor-ldpc-checks-force-dense-noncommutation
  - bounded-type-noncentral-code-sectors-round-uniformly
---

Fix a nonabelian factor `f` and choose `j` for which

```text
U_j={i:[Q_i^(f),Q_j^(f)]!=0}
```

is nonempty.  If a parity row met `U_j` only at `s`, its exact commuting
product relation would express `Q_s^(f)` as a product of reflections all
commuting with `Q_j^(f)`, a contradiction.  Thus `U_j` is a stopping set.
The all-local-dual DELL​M presentation has no nonempty stopping set below
`alpha L`, so `|A_f|>=|U_j|>=alpha L`.

Summing over nonabelian factors and reversing the order of summation gives

```text
alpha L # {nonabelian f}
 <= sum_f |A_f|
 = sum_i # {f:i in A_f}
 <= B L.
```

This proves the factor count.  Irreducible degrees multiply under tensor
products, abelian factors contribute degree one, and direct sums take the
maximum degree.  The bounded-type rounding theorem then gives the asserted
exclusion.
