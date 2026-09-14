---
rg: 2
id: leavitt-rooted-defect-window-carries-no-strict-design
kind: claim
title: The rooted defect window over the Leavitt unit group carries no strict design, because its two-rectangle table group is Z * Z/2
requires:
  - two-rectangle-surjunctive-images-kill-all-designs
distinct_from:
  defect-window-automaton-over-leavitt-units: that asks for a strict pair whose Garden of Eden sits on the defect pair; this excludes every design whose memories are the smallest window realizing that node's rooted identification, over any alphabet.
  small-leavitt-invariant-output-windows-have-finite-separations: that screens invariant-output designs on 45 ball windows; this excludes all designs on one defect window through both product rectangles.
artifacts:
  - research/artifacts/gk3-leavitt-nonlinear-2026-09-14.md
  - experiments/gk3-leavitt-nonlinear/defect_direct_tables.py
---

**ESTABLISHED.** Let `G = L_(F_2)(1,2)^x`. Take:
- `cu`, the compressor of `openai-nine-leaf-leavitt-configuration`;
- `c`, the `x_0` of Thompson's `F` on the cylinder `[1000]`;
- `a = cu c^-1 cu^-1`;
- `l = E_01(1) = 1 + S[alpha_0] T[alpha_1]`.

Put

```text
S = {1, a, a^-1, a l},        M = {1, l, a}.
```

This is the smallest window realizing the rooted identification `(a l^-1, l) ~ (1, a)` of
`defect-window-automaton-over-leavitt-units`. The defect `d = [cu c cu^-1, l]` is
nontrivial.

**Theorem.** For every finite alphabet and all rules `nu` on `S` and `mu` on `M`, the pair
`(tau, sigma)` over `G` with `sigma tau = id` has `tau` surjective.

## Proof

1. **Exact product tables** (`experiments/gk3-leavitt-nonlinear/defect_direct_tables.py`).
   These use normal-form products in the shared checker, with every product recomputed on
   the second, prefix-table path: 288 products cross-checked, no disagreement.
   - `l^2 = 1` and `l != 1`; `a^k != 1` for `k = 1..8`; `d != 1`.
   - Forward rectangle `S x M`: 8 classes of 12. The only coincidences are
     `(1,1) = (a^-1, a)`, `(1,a) = (a,1) = (al, l)` and `(a,l) = (al, 1)`.
   - Reverse rectangle `M x S`: 10 classes of 12. The only coincidences are
     `(1,1) = (a, a^-1)` and `(1,a) = (a,1)`.
2. **The table group.** The letters are `x_a` (for `a` in `S ∩ M`), `x_(a^-1)`,
   `x_(al)` and `x_l`. The relators are:
   - `x_(a^-1) x_a = 1` and `x_a x_(a^-1) = 1`;
   - `x_a = x_(al) x_l` and `x_a x_l = x_(al)`;
   - `x_a = x_a`, which is trivial.

   Eliminating `x_(a^-1)` and `x_(al)` leaves `x_a = x_a x_l^2`, so
   `T = <x_a, x_l | x_l^2 = 1> = Z * Z/2`.
3. **Separation.** A free product of residually finite groups is residually finite.
   The 10 reverse classes are distinct in `G`, hence distinct in `T`. So a finite image of
   `T` separates them: one quotient per pair, combined in the direct product.
4. **Conclusion.** Finite groups are surjunctive. Apply
   `two-rectangle-surjunctive-images-kill-all-designs`. QED

## Scope

- **This window.** A strict pair built on this identification needs larger memories, and
  their forced coincidences must make some reverse hinge word die in every sofic image of
  the two-rectangle table group.
- **Not the defect node.** It says nothing about windows containing the Kazhdan subgroup
  `Gamma` or the nesting relators.
