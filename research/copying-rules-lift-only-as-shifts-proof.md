---
rg: 2
id: copying-rules-lift-only-as-shifts-proof
kind: route
title: The site encoding intertwines the copying rule with a right shift, copy automata are shifts by right cancellation, and eps-fixed configurations are already in the image
target: copying-rules-lift-to-clifford-covers-only-as-shifts
requires:
  - injective-automata-restrict-to-schreier-graph-automata
  - clifford-cover-cofinite-lamp-subgroups-contain-the-center
artifacts:
  - research/artifacts/clifford-copying-rule-lift-2026-09-12.md
---

Complete direct proof, artifact Section 1.
- **Lift.** `R(iota x)(e) = x(pi(e) t^(-1) Gamma) = x(p(pi(e) Gamma)) = iota(rho x)(e)`; the shift by `s^(-1)` inverts
  `R`.
- **Invariance.** `ker pi` acts trivially on `X`, so equivariance gives `L_k phi(x) = phi(x)`.
- **Copy automata.** The cells `e m` are distinct by right cancellation. The copied cell lies in `eM`, `mu` is the
  projection onto its coordinate, and `mu` does not depend on `e`, so the coordinate is fixed.
- **Clifford covers.** `Fix_H <= Fix_(eps)`. Part 4 of the restriction theorem, with `G/<eps> = W` surjunctive, puts
  `Fix_(eps)` in the image; part 1 gives `tau(Fix_H) = image cap Fix_H = Fix_H`. Cofinite lamp parts contain `eps`
  by the cofinite-lamp node.
