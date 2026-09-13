---
rg: 2
id: rover-nekrashevych-groups-have-co-re-word-problem-proof
kind: route
title: "Prefix-computation proof that Röver–Nekrashevych groups of finitely generated self-similar groups have co-r.e. word problem"
target: rover-nekrashevych-groups-have-co-re-word-problem
requires: []
---

Write `A = {0, ..., d−1}`, `A^*` for finite words and `A^ω` for the Cantor space.

**Finite data for `G`.** Fix generators `s_1, ..., s_k` of `G`. Each `s_i` acts
by `s_i(x w) = s_i(x) · (s_i|_x)(w)` with `s_i(x) ∈ A` and `s_i|_x ∈ G`. Fix
words `σ_{i,x}` in `s_1^{±1}, ..., s_k^{±1}` representing the sections
`s_i|_x`, and similarly for the inverses. For a word `w` in the `s_i^{±1}` and
a string `u ∈ A^n`, the image `w(u) ∈ A^n` is computable by recursion on `n`:
apply the letters of `w` right to left, using
`s(x u') = s(x) · σ_{s,x}(u')`, where `σ_{s,x}(u')` has strictly shorter input.

**Finite data for `K`.** An element `t ∈ V_d(G)` is given by two complete prefix
codes `{u_1, ..., u_m}` and `{v_1, ..., v_m}` in `A^*` and labels `g_1, ..., g_m`
in `G`. It acts by `u_j y ↦ v_j g_j(y)`. Fix generators `t_1, ..., t_p` of `K`,
with such data for each `t_l^{±1}` and the labels written as words in the `s_i`.
For a string `u` with a prefix `u_j`, set `t(u) = v_j g_j(u')` where `u = u_j u'`.
Then `t` maps the cone `[u]` into the cone `[t(u)]`, and
`|t(u)| ≥ |u| − L`, where `L` bounds the code lengths over all generators and
inverses. If `u` is shorter than every code word it prefixes, `t(u)` is
undefined.

**Semi-decision procedure.** Given a word `W = t_{l_1}^{±1} ⋯ t_{l_r}^{±1}`,
enumerate all strings `u ∈ A^*`. Try to compute `W(u)` by applying the letters
right to left. Accept if every step is defined and `W(u)` is incomparable with
`u` (neither is a prefix of the other).

- **Soundness.** If `W(u)` is defined and incomparable with `u`, then for every
  `y ∈ [u]` the point `W(y)` lies in `[W(u)]`, which is disjoint from `[u]`, so
  `W(y) ≠ y` and `W ≠ 1`.
- **Completeness.** If `W ≠ 1` then, because `V_d(G)` is a group of
  homeomorphisms of `A^ω`, some `y` has `W(y) ≠ y`. Say they differ at position
  `q`. Take `u` a prefix of `y` of length at least `q + 1 + rL`. Every step is
  defined, since each intermediate string still has length at least `L`. The
  output `W(u)` is a prefix of `W(y)` of length at least `q + 1`. Both `u` and
  `W(u)` include position `q`, where they differ, so they are incomparable.

Therefore the set of non-identity words is recursively enumerable. A word in
the generators of a finitely generated subgroup of `V_d(G)` is a word in the
`t_l`, so the conclusion applies to every finitely generated subgroup,
including `G`, `V_d` and the finite-index commutator subgroups.
