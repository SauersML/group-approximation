---
rg: 2
id: single-fibre-garden-of-eden-transplant-proof
kind: route
title: Transplant along a sofic model, store the bad points, and compress the output columns by the missing single-fibre pattern
target: strict-product-automata-have-no-single-fibre-garden-of-eden
requires: []
artifacts:
  - research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md
---

Sections 1–2 of the artifact.

- **Exact at good points.** At good points of a `(P, epsilon)`-model the addresses `(g g_n g_m, v.(k_n k_m))`
  have exactly the coincidences of `G x K`. So the transplanted decoder identity holds, and transported
  Garden of Eden patterns stay missing.
- **Repair.** `Psi(y)(g) = (tau_V(y)(g), y(g)|_(V_bad))` is injective over `G`.
- **Column count.** A pattern `p` on `E <= {1} x K` is missing on at least `(1 - epsilon)|V| / (|E_K|^2 + 1)`
  disjoint blocks `v.E_K` of every output column. So the output alphabet has at most
  `q^|V| (1 - q^(-|E|))^((1-epsilon)|V|/(|E_K|^2+1)) q^(epsilon |V|) < q^|V|` symbols for small `epsilon`
  and large `|V|`.
- **Contradiction.** Composing with a symbolwise injection into `A^V` gives a strict automaton over `G`.
