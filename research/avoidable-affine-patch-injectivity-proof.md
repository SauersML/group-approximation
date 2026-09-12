---
rg: 2
id: avoidable-affine-patch-injectivity-proof
kind: route
title: Choose values avoiding the patched symbol on both sides of a kernel element of the linear part
target: avoidable-patches-of-affine-rules-inherit-linear-injectivity
requires: []
artifacts:
  - research/artifacts/small-memory-balance-census-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Section 5.1 of the artifact.
- **Kernel element.** Take `d != 0` in the kernel of the linear automaton.
- **Avoid the patched symbol.** Pick `x(g)` outside `{s, s - d(g)}`, which is possible because
  `q >= 3`. Then `x` and `x + d` never show the symbol `s`.
- **Collision.** On both configurations the patched automaton equals the affine one, and the
  affine images agree. So the patched automaton is not injective.
- **Dichotomy.** A surjective injective linear automaton is bijective. Its inverse is linear, and
  composition of linear automata is multiplication in `F_q[G]`, so the linear part is a unit.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently, including the unit
example `(a(1 - c))^3 = 0` over `Z x Z/3` (`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`,
Section 9.3).
