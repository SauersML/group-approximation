---
rg: 2
id: atiyah-amalgam-rank-from-cohn-coproduct
kind: claim
title: Strong Atiyah for an amalgam follows from integrality of one rank function on the coproduct of vertex division closures
distinct_from:
  atiyah-amalgam-unmixed-matrices-reduce-to-factors: that handles matrices supported in one vertex or the edge by induction; this reduces every matrix over the amalgam to one rank function on the ring coproduct of the vertex division closures over the edge division closure, where the vertex-mixing matrices live.
  atiyah-kazhdan-edge-blocks-both-permanence-routes: that records why two proof frameworks fail at a property (T) edge; this is a framework-free reduction that uses no hypothesis on the edge group.
  atiyah-passes-to-torsion-free-elementary-amenable-extensions: that is permanence under torsion-free elementary amenable quotients; this is a reduction statement for amalgamated free products with arbitrary edge.
artifacts:
  - research/artifacts/atiyah-vertex-mixing-2026-09-12.md
---

**ESTABLISHED** by [[atiyah-amalgam-rank-cohn-coproduct-proof]].

Let `K` be a subfield of `C` closed under complex conjugation, let `G = A *_C B`, and write
`D_H` for the division closure of `K[H]` in the algebra `U(H)` of affiliated operators. Then:

1. `D_C <= D_A` and `D_C <= D_B` inside `U(G)`.
2. There is a unique ring homomorphism

   ```text
   phi: R := D_A *_(D_C) D_B  ->  U(G)
   ```

   extending the inclusions, and a ring homomorphism `psi: K[G] -> R` with `phi o psi` equal to
   the inclusion `K[G] <= U(G)`.
3. If `rk_G(phi(Y))` is an integer for every matrix `Y` over `R`, then `G` satisfies the Strong
   Atiyah conjecture over `K`.
4. `rk_G(phi(Y)) <= rho_R(Y)` for every `Y`, where `rho_R` is the inner rank of `R`. So equality
   for all `Y` implies Strong Atiyah over `K` for `G`. Every matrix over `K[G]` with non-integral
   kernel dimension is rank deficient after `psi`: `rk_G(M) < rho_R(psi(M))`.

No hypothesis on `C` is used. The theorem relocates the vertex-mixing case of Strong Atiyah,
the open part after [[atiyah-amalgam-unmixed-matrices-reduce-to-factors]] and
[[atiyah-kazhdan-edge-blocks-both-permanence-routes]], to the single homomorphism `phi`.

Context, not used in the proof. By Linnell's criterion the converse of (3) holds for
torsion-free `G`. By Cohn's coproduct theorem, when the factors satisfy Strong Atiyah, `R` is a
semifir whose universal field of fractions has rank function `rho_R`. Neither statement was
re-read from the source.
