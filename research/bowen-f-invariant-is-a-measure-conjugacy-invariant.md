---
rg: 2
id: bowen-f-invariant-is-a-measure-conjugacy-invariant
kind: claim
title: Bowen's f-invariant of finite generating partitions is a measure-conjugacy invariant of free group actions
distinct_from:
  free-group-injective-ca-preserve-bernoulli-via-f-invariant: that applies the invariant to injective cellular automata; this is the imported invariance theorem itself.
artifacts:
  - research/artifacts/free-group-f-invariant-bernoulli-preservation-2026-09-12.md
---

Let `F_r = <s_1, ..., s_r>` act by measure-preserving transformations of a probability
space. For a finite partition `alpha` put
`F(alpha) = (1-2r)H(alpha) + sum_i H(alpha v s_i alpha)` and
`alpha^n = v_{g in B(e,n)} g alpha`. For every finite generating partition the limit
`f(alpha) = lim_n F(alpha^n)` exists. Any two finite generating partitions of the same
action give the same value.

For a Bernoulli shift with the coordinate partition, `f` equals the Shannon entropy of
the base.

**Source.** L. Bowen, *A measure-conjugacy invariant for free group actions*, Ann. of
Math. 171 (2010), 1387–1400. The invariance proof uses no sofic approximation. Monotonicity
of `F` under splitting is re-derived in Section 2 of the artifact. The invariance
statement is imported as quoted, and its proof was not re-derived here.

**ESTABLISHED 2026-09-12** by [[bowen-f-invariant-citation]].
