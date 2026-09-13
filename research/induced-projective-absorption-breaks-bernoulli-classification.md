---
rg: 2
id: induced-projective-absorption-breaks-bernoulli-classification
kind: claim
title: If a free F_p[G]-module absorbed a nonzero module induced from finite subgroups, base entropy would fail to classify Bernoulli shifts over G (vacuous)
distinct_from:
  stable-finiteness-failure-is-algebraic-bernoulli-absorption: that gives, from any one-sided inverse, a Bernoulli shift absorbing a nontrivial algebraic factor; this is the special shape where the factor is co-induced from finite subgroups, which never occurs.
  bernoulli-entropy-counterexample-constraints: that proves necessary conditions on a counterexample group; this is a sufficient algebraic condition that no group satisfies.
  finite-subgroup-induced-absorption-conserves-entropy: that is the obstruction showing the hypothesis here is never met; this is the implication itself.
artifacts:
  - research/artifacts/bernoulli-negative-induced-absorption-2026-09-12.md
---

**ESTABLISHED as an implication (unreviewed). THE HYPOTHESIS NEVER HOLDS.** When this node landed at
d2a8ad5ce4 it was read as a reduction of the negative direction to algebra. That reading was wrong.
`finite-subgroup-induced-absorption-conserves-entropy` shows, through the lifted p-adic trace, that no group
satisfies the hypothesis. Route: [[induced-projective-absorption-breaks-classification-proof]].

**Theorem E.** Let `G` be a countable group, `p` a prime, `n >= 1`, `F_1, ..., F_r <= G` finite subgroups,
and `Q_i` finite-dimensional `F_p[F_i]`-modules, not all zero, with

    F_p[G]^n ≅ F_p[G]^n ⊕ ⊕_i F_p[G] ⊗_(F_p[F_i]) Q_i       (left modules).

Put `rho = sum_i dim(Q_i)/|F_i|`. Then the Bernoulli shifts over `G` with base entropies `n log p` and
`n log p + rho log p` are isomorphic.

**What survives.**
- The proof composes duality with the co-induced Ornstein theorem
  `coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli`. Both are valid.
- Its failure teaches one thing: the entropy that co-induced isomorphisms add is the lifted trace, and module
  isomorphisms conserve it.
- The necessary conditions of Section 3 of the artifact, no trivial quotients and `rho ≡ 0 mod p`, are
  weaker than the lifted trace, which forces `rho = 0` exactly.
