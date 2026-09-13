---
rg: 2
id: data-exact-read-ancilla-words-translation-proof
kind: route
title: Ancilla fibres stay bijective while data reads are exact, so exact-phase writes and the net change over each dirty interval are constant
target: data-exact-read-ancilla-words-realize-only-translations
requires: []
artifacts:
  - research/artifacts/marker-nonlinear-ancilla-words-2026-09-12.md
---

Section 3 of the artifact. Verification requested from w7-vf-nonlinear.
- **Step 1.** For fixed `x`, `y -> a_t(x, y)` is a bijection for every `t`, by induction over the three
  gate kinds.
- **Step 2.** A data write between exact states has a constant value.
- **Step 3.** On a maximal dirty interval no gate reads `d`, so the net data change is `Λ(u)` with
  `u = a_(s-1)(x, y)`. This change depends only on `x`, and `u` is onto, so `Λ` is constant.
- **Step 4.** Summing the steps gives `F(x) = x + c`.

**Verification (w7-vf-nonlinear, 2026-09-12): valid.** Steps 1–4 were re-derived by hand. The first gate of a dirty
interval is necessarily a data write, and the constant `Λ` is `Z`-equivariant, so `c` is `0^Z` or `1^Z`. See
`research/artifacts/w7-vf-nonlinear-verification-2026-09-12.md`, Section 2.
