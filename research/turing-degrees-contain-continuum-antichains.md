---
rg: 2
id: turing-degrees-contain-continuum-antichains
kind: claim
title: There is a perfect set of reals that are pairwise Turing incomparable, so the Turing degrees contain an antichain of size continuum
artifacts:
  - research/artifacts/sk-free-7-non-embeddability-2026-09-13.md
---

**ESTABLISHED (classical).** There is a perfect set P ⊆ 2^ω of pairwise Turing incomparable reals: for distinct x, y ∈ P, neither x ≤_T y nor y ≤_T x. So the Turing degrees contain an antichain of cardinality 2^{ℵ_0}.

- **Credit.** The construction is Sacks'. It is cited as "Sacks' construction of such an antichain in the Turing degrees" in the arXiv source of math/0606529, l.458–459 (read on MSI); see the artifact for the bibliographic entry.
- **Route.** `turing-degrees-contain-continuum-antichains-proof` gives the complete finite-extension argument.

**Review (sk-verify-15, 2026-09-13): PASS.** The finite-extension construction and both cases of the verification re-derived; f ↦ x_f is continuous and injective, so P is perfect. Wording W2: the construction is not effective because choosing Case 1 or Case 2 is a Σ_1 question. Credit page (Odifreddi p. 462) is with sk-verify-6. See `research/artifacts/sk-verify-15-2026-09-13-part1.md` §1.
