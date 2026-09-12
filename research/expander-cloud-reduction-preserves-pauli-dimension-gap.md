---
rg: 2
id: expander-cloud-reduction-preserves-pauli-dimension-gap
kind: claim
title: Expander clouds degree-reduce Pauli games without losing their dimension gap
distinct_from:
  pauli-braiding-test-exponential-dimension: that supplies the original robust high-dimension game; this replaces its high-occurrence question incidences by bounded-degree occurrence clouds.
  bounded-neighbor-pauli-needs-growing-equality-components: that proves growing equality components are necessary for a pairwise Pauli dimension witness; this proves expander equality clouds are sufficient to preserve an existing witness.
---

Let `P_N` be a family of reflection games with perfect completeness, test
arity at most `k`, and constants `eta_0>0`, `D_N->infinity` such that value
above `1-eta_0` forces local dimension at least `D_N`.  Replace every
logical observable `q` by one occurrence `A_(q,t)` for every test `t`
containing it.  Connect the occurrences of each fixed `q` by a fixed-degree
expander of normalized spectral gap at least `lambda>0`, and add reflection
equality tests on those edges.  Use the designated occurrences in each old
test.

After harmless bounded padding/regularization of the incidence distribution,
the resulting games `P_N^deg` have bounded occurrence degree independent of
`N`, perfect completeness, and constants `eta_1>0`, `c>0` independent of
`N` such that

```text
value(P_N^deg)>1-eta_1  ==>  local dimension >= D_N.             (ECD1)
```

No tensor factor or direct-sum sheet is added in the decoding.  The same
finite-dimensional Hilbert space supports the decoded strategy for `P_N`.
Thus replacement by expander clouds is a dimension-preserving degree
reduction suitable for the occurrence compiler.

