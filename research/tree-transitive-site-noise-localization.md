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
- `relative-fixed-algebra-payment-lemma` identifies the exact analytic datum
  missing after a marked carrier has positive density. If `p` is the carrier
  and `N` is the full joint packet commutant, one must prove a uniform
  no-capture estimate
  `||E_N(p)||_2^2 <= (1-gamma)tau(p)` and charge the resulting covariance
  commutators to boundedly many defining relators. Positive trace alone is
  insufficient: a projection in the external multiplicity reservoir lies in
  `N` and pays zero adjoint energy.
- `generator-column-pauli-test-globalizes-but-does-not-pin-sites` supplies a
  sharp positive/negative benchmark.  The corrected de la Salle code-column
  test globally exactifies the whole `n`-site Pauli factor with explicit
  dimension-free HS constants.  But a zero-loss conjugacy
  `exp(i theta Z_1...Z_n)` moves every named `X_i`, and a multiplicity-valued
  version moves the whole factor relative to external tape words.  Hence the
  missing assertion here is not abstract tensor recovery; it is incidence
  which pins that recovered factor to the tree-addressed computation.
