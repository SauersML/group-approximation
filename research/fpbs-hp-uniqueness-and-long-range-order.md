---
rg: 2
id: fpbs-hp-uniqueness-and-long-range-order
kind: claim
title: A subgroup has a unique infinite-intersection cluster exactly when connectivity along it does not decay
artifacts:
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
---

**ESTABLISHED (imported).** Let `G` be a Cayley graph of a group `Gamma` and let
`H <= Gamma` be an infinite subgroup. A cluster `K` is `H`-infinite when
`|K ∩ H| = infinity`. For each `p in [0,1]`, Bernoulli bond percolation `G_p` has
a unique `H`-infinite cluster almost surely if and only if

```text
inf_{x,y in H} P_p(x <-> y) > 0.
```

With `H = Gamma` this is the Lyons--Schramm equivalence of uniqueness with
long-range order.

Source: Hutchcroft--Pan, arXiv:2409.12283v1, Theorem 1.4 ("Uniqueness and
long-range order"), read from the PDF text on MSI on 2026-09-12. The proof uses
Timár's theorem that two infinite clusters meet in finitely many places almost
surely.

Status records an imported theorem, not independent mathematical verification.
