---
rg: 2
id: linear-invariant-output-automata-fail-augmentation
kind: claim
title: Linear automata with right-coset-invariant output die by augmentation in modular characteristic and are corner compressions otherwise
distinct_from:
  central-c3-quadratic-surjunctivity-iff-direct-finiteness: that proves a quadratic Boolean family on central three-cycles equivalent to scalar direct finiteness; this classifies linear automata whose outputs are constant on right cosets of any finite subgroup, by augmentation or by an idempotent compression.
  invariant-output-injective-automata-need-invisible-symmetry: that is a permutation-model obstruction for all automata of this shape; this is an algebraic obstruction for the linear ones only, valid over every group including nonsofic ones.
artifacts:
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

Let `k` be a finite field of characteristic `p`, `G` any group, `H` a finite
subgroup, and `a` in `k[G]` with `tau_a(x)(g) = sum_m a_m x(gm)`.

1. The output of `tau_a` is right-`H`-invariant iff `ha = a` for all `h` in `H`.
2. If `p` divides `|H|`, no such `tau_a` is injective, over any group. The
   coefficients are constant on free left `H`-orbits, so `eps(a) = 0`, while an
   injective `tau_a` has `ca = 1` for some `c`.
3. If `p` does not divide `|H|`, let `e` be the averaging idempotent of `H`.
   Such an injective `tau_a` exists iff `c e b = 1` for some `b,c` in `k[G]`.
   For `H != 1`, `(eb)c != 1`, so this is a direct-finiteness failure of
   corner-compression type.

So over `F_2`, an output invariant under an involution is available only to
genuinely nonlinear rules. The odd-order case returns to the corner questions of
`order-three-axis-feedback-surjunctivity-iff-corner-finiteness`. Proof:
Section 2 of the linked artifact, Proposition C.
