---
rg: 2
id: fpbs-hermon-hutchcroft-anchored-expansion
kind: claim
title: Every infinite cluster of supercritical Bernoulli bond percolation on a nonamenable transitive graph has anchored expansion
distinct_from:
  fpbs-supercritical-finite-susceptibility: that records the exponential tail of finite clusters (Theorem 1.1 of the same paper) and its sum; this records the isoperimetric consequence for infinite clusters (Corollary 1.4), which is about the infinite cluster itself
  fpbs-hermon-hutchcroft-supercritical-analyticity: that is analyticity of finite-cluster observables (Corollary 1.3); this is anchored expansion of infinite clusters (Corollary 1.4)
---

**Published input.** Let `G` be a connected, locally finite, nonamenable,
transitive graph and let `p_c(G) < p <= 1`. Then almost surely every infinite
cluster `K` of Bernoulli-`p` bond percolation on `G` has anchored expansion,
that is

```text
Phi*_E(K) = lim_(n -> infinity) inf { |d_E S| / sum_(u in S) deg_K(u) :
             S subset V(K) connected, v in S, n <= |S| < infinity } > 0,
```

where `d_E S` is the set of edges of `K` with exactly one endpoint in `S`,
`deg_K` is the degree in `K`, and the value does not depend on the vertex `v`
of `K`.

Every Cayley graph of a finitely generated nonamenable group satisfies the
hypotheses.

Imported by `fpbs-hermon-hutchcroft-anchored-expansion-citation`.
