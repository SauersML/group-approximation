---
rg: 2
id: rokhlin-supremum-dichotomy-with-centralized-self-copies
kind: claim
title: Unbounded finite subgroups centralizing a finite-supremum subgroup force zero Rokhlin entropy supremum
distinct_from:
  positive-rokhlin-entropy-action-gives-positive-supremum: that is Seward's equivalence of positive-entropy conditions for one group; this is a vanishing theorem for groups containing a centralized subgroup of finite supremum, and a zero-or-infinity dichotomy for groups containing their own square.
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

**Theorem.** Let `Gamma` be a countably infinite group. Suppose `Gamma` contains

* an infinite subgroup `G` with `h^Rok_sup(G) < infinity`, and
* finite subgroups `T_n` with `|T_n| -> infinity`, each commuting elementwise with `G` and meeting `G` trivially.

Then `h^Rok_sup(Gamma) = 0`.

**Corollary (self-copies).** Suppose `Gamma` contains a subgroup isomorphic to `Gamma x Gamma` and has finite subgroups of unbounded order. Then `h^Rok_sup(Gamma)` is `0` or `infinity`. So POS(`Gamma`), INF(`Gamma`) and RBS(`Gamma`) are equivalent, and each makes `Gamma` surjunctive with `K[Gamma]` directly finite for every field `K`.

For `Gamma = P x G` the theorem is Seward's Theorem 6.7 (arXiv:1501.03367v4). His proof uses the direct product only through a finite `T <= P` that commutes with `G` and meets it trivially, so it transfers verbatim. Full proof: Section 1 of the artifact.

The corollary takes `G` to be the first factor of the embedded square and the `T_n` inside the second factor. Its equivalences use `positive-rokhlin-entropy-action-gives-positive-supremum` and `infinite-rokhlin-supremum-forces-surjunctivity`.

Examples are the binary Leavitt unit group (`positive-rokhlin-entropy-makes-leavitt-units-surjunctive`) and Thompson's group `V`. The theorem gives no lower bound on Rokhlin entropy, and it does not decide which side of the dichotomy any nonsofic group lies on.
