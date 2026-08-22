---
rg: 2
id: bounded-prefix-decision-cost-forces-bounded-approximate-rank
kind: claim
title: Bounded expected prefix decision cost forces dimension-independent approximate rank
distinct_from:
  dense-offdiagonal-packet-has-linear-dimensional-average-models: that gives one explicit character-table collapse for the complementary identity kernel; this applies to every classical prefix-stopping kernel.
  lin-code-space-pauli-test-has-only-logarithmic-weyl-rank: that computes the exact rank of one literal code-space test; this bounds approximate rank from the stopping complexity of an arbitrary binary prefix predicate.
---

**ESTABLISHED.**

Let `K_n:{0,1}^n x {0,1}^n -> F_2` be a Boolean matrix.  Suppose a
deterministic prefix procedure reads the two words synchronously, stops at a
stopping time `L_n(u,v)<=n`, and outputs `K_n(u,v)`.  If

```text
sup_n E_(u,v) L_n(u,v) <= C,                             (BPD1)
```

then for every `epsilon>0` there is a Boolean matrix `K'_n`, differing from
`K_n` on at most an `epsilon` fraction of entries, with

```text
rank_(F_2)(K'_n) <= 2^ceil(C/epsilon).                   (BPD2)
```

If instead `sup E L_n^2<=C_2`, the right side improves to
`2^ceil(sqrt(C_2/epsilon))`.

Consequently no family whose symplectic rank remains unbounded after an
arbitrarily small fixed fraction of entry errors can be certified by a
classical prefix calculation of uniformly bounded expected cost.  In
particular, replacing the sparse diagonal phase in a dual-prefix Heisenberg
packet by any bounded-average prefix predicate cannot simultaneously retain
a robust growing-rank Weyl obstruction.  The rare deep cells necessarily
carry the rank information.

This is an information-theoretic obstruction, independent of the chosen
Leavitt or Toeplitz groupification.  A live constant-loss construction must
leave the deterministic prefix-stopping model--for example through a
quantum/code test whose robust rank is not approximated by truncating a
classical decision tree--or must separately amplify the deep-cell energy.

