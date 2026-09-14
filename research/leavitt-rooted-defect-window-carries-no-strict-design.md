---
rg: 2
id: leavitt-rooted-defect-window-carries-no-strict-design
kind: claim
title: The rooted defect window over the Leavitt unit group carries no strict design, because its two-rectangle table group is Z * Z/2
distinct_from:
  defect-window-automaton-over-leavitt-units: that asks for a strict pair whose Garden of Eden sits on the defect pair; this excludes every design whose memories are the smallest window realizing that node's rooted identification, over any alphabet.
  small-leavitt-invariant-output-windows-have-finite-separations: that screens invariant-output designs on 45 ball windows; this excludes all designs on one defect window through both product rectangles.
artifacts:
  - research/artifacts/gk3-leavitt-nonlinear-2026-09-14.md
  - experiments/gk3-leavitt-nonlinear/defect_direct_tables.py
---

**ESTABLISHED** by `leavitt-rooted-defect-window-no-strict-design-proof`.

Let `G = L_(F_2)(1,2)^x`. Take:
- `cu`, the compressor of `openai-nine-leaf-leavitt-configuration`;
- `c`, the `x_0` of Thompson's `F` on the cylinder `[1000]`;
- `a = cu c^-1 cu^-1`;
- `l = E_01(1) = 1 + S[alpha_0] T[alpha_1]`.

Put

```text
S = {1, a, a^-1, a l},        M = {1, l, a}.
```

This is the smallest window realizing the rooted identification `(a l^-1, l) ~ (1, a)`
of `defect-window-automaton-over-leavitt-units`. The defect `d = [cu c cu^-1, l]` is
nontrivial.

**Theorem.** For every finite alphabet and all rules `nu` on `S` and `mu` on `M`, the
pair `(tau, sigma)` over `G` with `sigma tau = id` has `tau` surjective.

**Why.**
- The exact product tables show only the forced coincidences.
- So the two-rectangle table group is `<x_a, x_l | x_l^2> = Z * Z/2`, which is residually
  finite.
- A finite image separates the reverse products, and
  `two-rectangle-surjunctive-images-kill-all-designs` applies.

**Scope.**
- **This window.** A strict pair built on this identification needs larger memories.
  Their forced coincidences must make some reverse hinge word die in every sofic image of
  the two-rectangle table group.
- **Not the defect node.** It says nothing about windows containing the Kazhdan subgroup
  `Gamma` or the nesting relators.
