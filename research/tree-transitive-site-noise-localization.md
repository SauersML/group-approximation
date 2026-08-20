---
rg: 2
id: tree-transitive-site-noise-localization
kind: claim
title: Tree-transitive local checks convert global HS defect into bounded adversarial site weight
distinct_from:
  clifford-hs-defect-becomes-adversarial-site-noise: that asks for the full tensor-factor repair theorem for an arbitrary polylog-addressed packet; this supplies the missing localization estimate in the Thompson-Nekrashevych architecture.
  bgv-adversarial-fault-tolerance: that starts after a bad-site set is already defined; this constructs and bounds that set from group relator energy.
---

For the level-`n` leaves of `nekrashevych-clifford-sign-tape`, let every local
cell test be an internal conjugate of one fixed bounded relator neighborhood.
After the uniform relative Clifford exactification, define a site bad when its
local defect exceeds a fixed repair threshold `eta`.

Prove, without assuming a tensor product in advance, that the good-site local
algebras admit one coherent tensor realization and that

```text
|B_n|/2^n <= C E/eta^2                                      (TSN1)
```

uniformly in `n`.  The first assertion handles coherent errors; the second is
the Markov bound made dimension-free by tree transitivity and bounded overlap.
Tree-recursive logical Pauli products must be represented by fixed group words
using relations of the form `h=x_0 s h s^(-1)`, and retain a mark floor after
any corruption below the BGV adversarial radius.

## Attempts

- Markov's inequality proves `(TSN1)` once site defects exist with bounded
  overlap. The unresolved step is simultaneous tensor-factor recovery:
  defining bad sites before coherent local algebras are aligned is circular.
- Pauli twirling is postponed until after recovery; twirling first assumes the
  tensor product this claim must prove.
- Test recursive logical relations on repetition and balanced-product code
  generators first, rejecting words with cost linear in the number of leaves.
