---
rg: 2
id: some-simple-kazhdan-lef-groups-are-not-exact-proof
kind: route
title: Osajda's residually finite non-exact group lies in a simple Kazhdan LEF host, and property A passes to subspaces
target: some-simple-kazhdan-lef-groups-are-not-exact
requires: [residually-finite-non-exact-groups-exist, lef-groups-embed-in-simple-kazhdan-lef-groups]
artifacts:
  - research/artifacts/sk-free-1-exactness-2026-09-13-part1.md
---

Derivation; full text in the artifact §1.
1. **Input.** `residually-finite-non-exact-groups-exist` gives a finitely generated residually finite group Γ without property A.
2. **Γ is LEF.** For each r, residual finiteness gives a finite-index normal N missing the finitely many nontrivial elements of B_r B_r^{-1}. The quotient map Γ → Γ/N is multiplicative and injective on B_r.
3. **Host.** `lef-groups-embed-in-simple-kazhdan-lef-groups` gives Γ ≤ G with G infinite, finitely generated, simple, Kazhdan and LEF.
4. **Coarse equivalence.** With finite generating sets, the identity (Γ,d_Γ) → (Γ, d_G restricted) is:
   - uniformly expansive: d_G ≤ C·d_Γ with C the maximal G-length of Γ's generators;
   - effectively proper: G-balls meet Γ in finite sets, on which d_Γ is bounded.

   So Γ is coarsely equivalent to a subspace of G.
5. **Property A.** It is a coarse invariant and passes to subspaces (Willett, arXiv:math/0612492, l.542 and l.1228–1229). If G had property A, so would Γ. So G has no property A.
6. **Exactness.** For countable discrete groups, property A is equivalent to exactness of C*_r (Guentner–Kaminker; Ozawa; quoted from arXiv:1406.5015 l.166). So G is not exact.
7. **Hyperlinearity.** G is LEF, hence sofic and hyperlinear, so L(G) ⊆ R^ω.
