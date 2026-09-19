---
rg: 2
id: fpbs-meet-thresholds-tend-to-pc-z3-below-pu-on-z3-free-z2-proof
kind: route
title: Collapse the Bass-Serre tree to a bridge tree of Z^3 cosets, read the meet as a Galton-Watson tree of local meets, and let the replica number kill its mean
target: fpbs-meet-thresholds-tend-to-pc-z3-below-pu-on-z3-free-z2
requires:
  - fpbs-meet-threshold-capped-by-amenable-relative-threshold
  - fpbs-hutchcroft-l2-gap-criterion
  - fpbs-kesten-square-lattice-pc-one-half
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-amenable-caps-2026-09-19.md
---

The complete proof is in Section 2 of the artifact.

1. **Structure (2.1).** Suppress the degree-2 vertices `gZ/2` of the
   Bass–Serre tree. The result is a simple tree `Q` whose vertices are the
   `Z^3`-cosets and whose edges are the t-edges. So:
   - every t-edge is a bridge;
   - a cluster meets a coset exactly in a cube-edge cluster;
   - distinct vertices of a coset have their t-edges going to distinct
     cosets.
2. **Items 1–2 (2.2).** No imports.
   - *Item 1.* Count the internal t-edges as a forest on the `c` cosets met,
     plus 2 boundary cube edges per coset piece.
   - *Item 2.* The automorphism `x ↦ tx` gives `theta <= 2P(A)`. Then the
     independent events `A`, `B` and `{e closed}` produce two infinite clusters
     with positive probability whenever `theta > 0`.
3. **Item 3 (2.3).** The local meets `L(v) = ∩_i C^i(v)` are i.i.d. across
   cosets, with `E|L| = Z_k(p) = sum tau_p^k`.
   - A non-root block has `Bin(|L|-1, p^k)` children.
   - Blocks are finite because `chi(p) < infinity` below `p_c(Z^3)`
     (`fpbs-hutchcroft-l2-gap-criterion` item 1, sharpness).
   - The Galton–Watson extinction criterion finishes the proof.
4. **Item 4 (2.4).**
   - *Upper bound:* `p_cap^(k) <= p_c(Z^3;G) <= p_c(Z^3)` by
     `fpbs-meet-threshold-capped-by-amenable-relative-threshold`, items 1–2.
   - *Lower bound:* `m_k(p) <= p^k(chi(p)-1) → 0` for fixed `p < p_c(Z^3)`.
   - *Value:* `p_c(Z^3) <= p_c(Z^2) = 1/2` by
     `fpbs-kesten-square-lattice-pc-one-half`.
5. **Item 5 (2.5).** Use the l1 Aizenman–Barsky bound
   `chi(p) >= (1-p)/(6(p_c(Z^3)-p))` (`fpbs-hutchcroft-l2-gap-criterion` item 2,
   `q = 1`). It gives `p(chi(p)-1) > 1` just below `p_c(Z^3)`, hence
   `theta_G > 0` there, and so `p_c(G) < p_c(Z^3)`. Then apply item 4.
