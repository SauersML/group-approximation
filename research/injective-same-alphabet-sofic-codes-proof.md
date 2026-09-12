---
rg: 2
id: injective-same-alphabet-sofic-codes-proof
kind: route
title: Fano and Shearer counting on sofic models pins the output law of an equal-alphabet almost everywhere injective code
target: injective-same-alphabet-sofic-codes-preserve-uniform-measure
requires: []
artifacts:
  - research/artifacts/non-expanding-sofic-cascades-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Direct proof, Section 2 of `research/artifacts/non-expanding-sofic-cascades-2026-09-12.md`.

1. **Finite windows.** Lusin–Souslin gives a Borel decoder. Approximate the decoder by a cylinder function on
   `D`, and then the encoder by a cylinder function on `W`, with combined error `2 eps` at every site.
2. **Deficit.** If the output law is not uniform, some finite `F` containing `1` carries entropy deficit
   `c > 0`, and the approximated output keeps it up to `|F| delta'(eps)`.
3. **Count.** Take a sofic model of `Q = {1} ∪ D ∪ W ∪ DW ∪ F ∪ FW` as a right action.
   - Fano at good points gives `H(y) >= |V|(log q - delta - eta log q)`.
   - Shearer over the sets `{v.f : f in F}` covers all but `|F| eta |V|` points at least `|F|` times, giving
     `H(y) <= |V|(log q - (1-eta)c/|F| + delta' + |F| eta log q)`.
   - Letting `eta -> 0` and then `eps -> 0` forces `c <= 0`.

Part 1 (`|B| >= |A|`) comes out of the same lower bound.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently: the approximation order,
the good-chart laws, the Shearer cover with multiplicity `|F|` off `|F| eta |V|` points, and the order of
limits (`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 10.1).
