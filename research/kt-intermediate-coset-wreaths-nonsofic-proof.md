---
rg: 2
id: kt-intermediate-coset-wreaths-nonsofic-proof
kind: route
title: Normalize the centralizer of Gamma and read off the lamp at the coset K
target: kt-intermediate-coset-wreaths-are-nonsofic
requires:
  - kun-thom-nonsofic-wreath
---

Suppose `W_K` is sofic.  Let `rho: W_K -> S_U` be a sofic representation
(Kun--Thom Definition 2.1: `tr rho(w) = 0` for `w != 1`), with lamps `a_x`,
`x in G/K`.  Put `sigma = rho|_G`, a sofic representation of `G`.

Since `Gamma <= K`, every `gamma in Gamma` fixes the coset `K`, so
`gamma a_K gamma^(-1) = a_K` in `W_K`, and `rho(a_K)` lies in the centralizer
`C_(S_U)(sigma(Gamma))`.

By Kun--Thom Theorem 4.1 (verbatim in `kun-thom-nonsofic-wreath` and its
source artifact), `sigma(G)` normalizes that centralizer, so
`rho(a_(gK)) = sigma(g) rho(a_K) sigma(g)^(-1)` commutes with `sigma(Gamma)`
for every `g in G`.  For `gamma in Gamma` this gives

```text
rho(a_(gamma g K) a_(gK)) = sigma(gamma) rho(a_(gK)) sigma(gamma)^(-1) rho(a_(gK)) = 1.
```

The trace condition forces `a_(gamma g K) a_(gK) = 1` in `W_K`, i.e.
`gamma g K = g K`.  So `g^(-1) Gamma g <= K` for all `g`, i.e. `N <= K`,
contrary to hypothesis.

Theorem 4.1 needs only `Gamma` infranormal in `G` with `Gamma`, `G` Kazhdan,
which is Kun--Thom Theorem E.  No property of `K` beyond `Gamma <= K` is used.
