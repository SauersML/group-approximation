---
rg: 2
id: constant-background-kills-unit-linear-defect-rules
kind: claim
title: A rule with one moved table entry, a unit linear part and a pattern omitting a symbol is not injective unless a memory translate is absorbed
distinct_from:
  avoidable-patches-of-affine-rules-inherit-linear-injectivity: that shows injectivity of a patched affine rule forces its linear part to be injective, hence a unit or a linear strict automaton; this kills the unit case outright for single-entry patches whose pattern omits a symbol, by an explicit pair of configurations.
  pair-distinct-ternary-rules-pre-injective-on-free-memory: that shows such rules have no finite invisible perturbation over free memory, where the linear part is not a unit; this uses the inverse of a unit linear part to build a finite invisible perturbation.
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `constant-background-kills-unit-linear-defect-rules-proof`.

**Theorem.** Let `mu(x) = sum_m c_m x_m + c_0 + t [x|_M = p]` over `F_q`, with `t != 0` and
`1` in `M`, over any group `G`. Suppose the linear part `ell = sum_m c_m m` is a unit of `F_q[G]`
with inverse supported on `N`, and `p` omits a symbol `c`. Suppose also that every translate
`hM`, `h != 1`, lying in `M ∪ N^-1` shows the pattern `p` in neither of the two configurations below.
Then the automaton is not injective.

**Witness.**
- `x` is the constant `c` off `M`, and `p + t (k_(m^-1))_m` on `M`.
- `x' = x - t K delta_1`, where `K` is the inverse automaton.
- `x'` has exactly one more defect, at `1`. Every other window with a site outside `M ∪ N^-1` reads a
  `c` there and shows no defect in either configuration.
- So `L x' + D(x') = L x + D(x)`.

**Consequences.**
- **Augmentation.** A unit has nonzero augmentation, so a linear part with coefficient sum `0` is
  never a unit.
- **Three ternary addresses with distinct identified pairs.**
  - Either the coefficients sum to `0`, and the rule is injective only over groups already carrying a
    linear strict automaton (`avoidable-patches-of-affine-rules-inherit-linear-injectivity`).
  - Or `p` omits a symbol, and the theorem applies.
- **The ternary example.** `x_1 + x_a + x_b + [x = (0,1,2)]` is of the first kind.
- **Backgrounds at a used symbol (Theorem 13').** For any symbol `c` with `P_c = {m : p_m = c}`, the
  same witness works unless some `h != 1` carries `M \ P_c` into `M ∪ N^-1` and shows `p` there.
- **What is left of the architecture.** Take an injective single-defect rule with a unit linear part.
  It needs, for every symbol `c`, a nontrivial translate of `M \ P_c` absorbed into `M ∪ N^-1` that
  shows `p`. Patterns using every symbol do not escape.

Artifact, Section 4.
