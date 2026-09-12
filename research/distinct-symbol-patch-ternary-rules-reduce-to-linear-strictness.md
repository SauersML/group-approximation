---
rg: 2
id: distinct-symbol-patch-ternary-rules-reduce-to-linear-strictness
kind: claim
title: A ternary three-address rule that differs from an affine rule at one pattern with three distinct symbols is injective only where its linear part is a linear strict automaton
distinct_from:
  single-patch-ternary-rules-reduce-to-linear-strictness: that settles patches with a repeated symbol and needs non-commuting memory; this settles patches with three distinct symbols, over every placement with no commutation hypothesis, by breaking the one dangerous translate at a second site and reading the obstruction off the linear equation.
  avoidable-patches-of-affine-rules-inherit-linear-injectivity: that transfers injectivity to the linear part; this also rules out a surjective linear part.
artifacts:
  - research/artifacts/distinct-symbol-patch-collision-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `distinct-symbol-patch-linear-reduction-proof`. Independent
re-derivation requested from `w3-vf-nonlinear`.

**Statement.** Let `A = F_3`, `G` a group, `M = {m_1, m_2, m_3}` three distinct elements of `G`, and
`lambda` affine with linear automaton `L`. Let `mu = lambda + epsilon [pattern = p]` with `p` a pattern
of three distinct symbols and `epsilon != 0`.
- **Not injective.** If `L` is surjective, `tau_mu` is not injective. If `L` is bijective, `tau_mu` is
  not even pre-injective.
- **Reduction.** If `tau_mu` is injective over `G`, then `L` is an injective, non-surjective linear
  automaton over `G`.

**Every single patch.** Together with `single-patch-ternary-rules-reduce-to-linear-strictness` and the
constant test, every ternary three-address rule that differs from an affine rule at exactly one pattern
is injective over `G` only if its linear part is a linear strict automaton over `F_3` on `G`
(artifact Corollary 3).

**Use.** This closes the case left open in Section 2.2 of
`single-patch-ternary-rules-linear-reduction-2026-09-12.md`, including its danger case. What remains
of `ternary-three-address-injective-automata-have-balanced-rules` is rules at distance at least 2 from
every affine rule.

Artifact, Sections 1 and 2.
