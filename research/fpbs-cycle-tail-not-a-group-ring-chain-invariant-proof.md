---
rg: 2
id: fpbs-cycle-tail-not-a-group-ring-chain-invariant-proof
kind: route
title: Place a short and a long chord on one pattern-isolated cylinder and compare them by path substitution
target: fpbs-cycle-tail-not-a-group-ring-chain-invariant
requires: []
artifacts:
  - research/artifacts/fpbs/docs/cycle-tail-unipotent-chord-swap-2026-09-17.md
---

The full proof is in Sections 2–4 of
`cycle-tail-unipotent-chord-swap-2026-09-17.md`.

1. **Chords.** Pick gamma_s with D = {d(x, gamma_s x) = 2} non-null, and
   gamma_l outside the finite label set F_L. Distance sets are clopen for
   cylinder graphings.
2. **Isolation.** A random-pattern cylinder C_omega on a set B disjoint
   from a cylinder inside D satisfies U cap kU = empty for a finite set K_0
   of forbidden shifts. The union bound uses rank >= n/2 for the
   constraints omega(ke) = omega(e). Intersect with
   G_M = {d(x, gamma_l x) <= M} for M large. This makes both new edge
   sets simple, of measure mu(U), and makes U cup gamma_l U L-isolated.
3. **W.** Path substitution sigma_s, sigma_l : N -> C_1(Phi) gives
   E = [[1, -sigma], [0, 1]] with partial^bullet E = (partial, 0). So
   W = E_l E_s^{-1} is unipotent over A. It preserves finitely supported
   cycles in both directions, so W Z(Phi_s) = Z(Phi_l), and
   E(Z(Phi) + N) = Z(Phi_bullet).
4. **Tails.** L-isolation gives z_L(Phi_l) = z_L(Phi). The triangles
   e_x - P_s(x) project onto N, so z_L(Phi_s) >= z_L(Phi) + mu(U).
   Together with z(Phi_s) = z(Phi_l) = z(Phi) + mu(U) from step 3, this
   gives item 3.

No imported identity is used. Status records a written elementary proof,
not independent validation.
