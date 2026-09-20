---
rg: 2
id: ct-p-z-neutral-primes-kourovka-21-74a-is-decidable-proof
kind: route
title: "Decide degeneracy of each flow component by a finite test on piece formulas; bound nondegenerate fibres by two conjugate hyperbolic holonomies; truncate radial structure around degenerate centers to one core ball; run the positive-ray search"
target: ct-p-z-neutral-primes-kourovka-21-74a-is-decidable
requires:
  - ct-p-z-positive-ray-kourovka-21-74a-is-decidable
  - ct-empty-z-kourovka-21-74a-is-decidable
  - ct-empty-z-cone-partition-question-is-decidable
---

Lane proof (bh-2174-rank2, 2026-09-19), not reviewed. The argument is in the body of
`ct-p-z-neutral-primes-kourovka-21-74a-is-decidable`. It uses:
- from the positive-ray node: the forest reduction, the skew product with neutral deep digits in
  the fibre, the finiteness of base candidates, and the torsion part (`ĝ^N = id` on `U × Φ`);
- from the V node: Lemmas B.1 and B.3, the basic fixed-point estimate, and the finite search with
  conditions 1–3 and its ⇐ direction;
- from the cone node: Lemma A and the computability of the flow components.

New ingredients: the degeneracy test (Lemma 1), the conjugate-holonomy bound for nondegenerate
components, the D1–D3 classification at degenerate centers, and radial truncation (Lemmas 2–3).
