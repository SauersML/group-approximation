---
rg: 2
id: fpbs-mohar-adjacency-norm-cheeger-bound-citation
kind: route
title: Lyons–Peres Theorem 6.7 gives rho at most sqrt(1 - Phi_E^2)
target: fpbs-mohar-adjacency-norm-cheeger-bound
requires: []
artifacts:
  - research/artifacts/fpbs/docs/expanding-factor-product-thresholds.md
---

Read on MSI on 2026-09-12 from the PDF of Lyons–Peres, *Probability on Trees and
Networks* (https://rdlyons.pages.iu.edu/prbtree/book.pdf), extracted with
`pdftotext`, Chapter 6.

* **Definition (Section 6.1).** For a network `(G,c,D)`, `|K|_D := sum_(x in K) D(x)`,
  `|∂_E K|_c := sum_(e in ∂_E K) c(e)`, and
  `Phi_E(G;c;D) := inf{ |∂_E K|_c / |K|_D ; ∅ ≠ K ⊂ V finite }`.
* **Norm equals spectral radius (Section 6.2).** "Thus, we have proved that the
  norm ||P|| equals the spectral radius, ... denoted ... rho(G)", for the network
  random walk on `l2(V,pi)`.
* **Theorem 6.7 (Expansion and Spectral Radius).** "Let (G,c,pi) be a connected,
  infinite network and Phi_E(G) := Phi_E(G;c;pi) be its edge-expansion constant.
  The spectral radius rho(G) of the associated network random walk satisfies
  Phi_E(G)^2/2 <= 1 - sqrt(1 - Phi_E(G)^2) <= 1 - rho(G) <= Phi_E(G)."
* **Notes, Section 6.10.** "We have incorporated an improvement due to Mohar (1988)."
* **Normalization (Section 6.4, remark after Theorem 6.18).** For an unweighted
  graph `Phi_E(G;1;deg)` "differs in the regular case by a factor of d_G from
  Phi_E(G;1;1)".

**Deduction.** Take `c ≡ 1`, so `pi = deg = d`. Then `P = A_G/d`, and `l2(V,pi)` is
`l2(V)` with the norm scaled by `sqrt d`, which does not change operator norms.
Also `Phi_E(G;1;deg) = h/d` with `h = Phi_E(G;1;1)`. Theorem 6.7 gives
`||A_G||/d = rho(G) <= sqrt(1 - h^2/d^2)`, that is, `||A_G|| <= sqrt(d^2 - h^2)`.
