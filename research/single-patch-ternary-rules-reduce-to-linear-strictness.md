---
rg: 2
id: single-patch-ternary-rules-reduce-to-linear-strictness
kind: claim
title: A ternary three-address rule that differs from an affine rule at one pattern with a repeated symbol is injective only where its linear part is a linear strict automaton
distinct_from:
  avoidable-patches-of-affine-rules-inherit-linear-injectivity: that transfers injectivity from a patched rule to its linear part; this also rules out a surjective linear part, through a collision built from a preimage of a delta, so the unit case dies and only linear strictness remains.
  constant-background-kills-unit-linear-defect-rules: that kills the unit case on a constant background, leaving a residue of absorbed memory translates inside M and N^-1; this fills the background greedily, keeping the repeated symbol out, so for patches that repeat a symbol the residue is empty over non-commuting memory.
artifacts:
  - research/artifacts/single-patch-ternary-rules-linear-reduction-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `single-patch-ternary-rules-linear-reduction-proof`. Independent
re-derivation requested from `w3-vf-nonlinear`.

**Statement.** Let `A = F_3`, `G` a group, and `M = {1, a, b}` with `1, a, b` distinct. Let `lambda` be
affine with linear automaton `L`. Let `mu = lambda + epsilon [pattern = (s_0, s, s)]`, with `s_0 != s`
and `epsilon != 0`.
- **Not injective.** If `a` and `b` do not commute and `L` is surjective, `tau_mu` is not injective.
  If `L` is bijective, `tau_mu` is not even pre-injective.
- **Reduction.** If `tau_mu` is injective over `G`, then `L` is an injective, non-surjective linear
  automaton over `G`.

Every affine three-address rule patched at one pattern that repeats a symbol takes this form after
permuting addresses and translating the placement.

**Use.**
- **The census rule.** The rigid rule `R` (`x - y + z` patched at `(0,2,2)`) is injective over `G`
  only if `x - y + z` is a linear strict automaton over `G`.
  - **Unit case.** When `1 - a + b` is a unit of `F_3[G]` and `a`, `b` do not commute, `R` is not
    even pre-injective.
- **No new counterexamples.** Single-patch rules of this kind give no counterexample beyond linear
  strict automata over `F_3`.

**Boundary.** Not covered:
- patches whose three symbols are distinct;
- rules at Hamming distance at least 2 from every affine rule.

Artifact, Sections 1 and 2.
