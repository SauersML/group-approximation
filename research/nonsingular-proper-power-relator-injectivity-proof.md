---
rg: 2
id: nonsingular-proper-power-relator-injectivity-proof
kind: route
title: Factor the coefficient map through the quotient by the root relator
target: nonsingular-injectivity-passes-to-proper-power-relators
requires: [torsion-free-amenable-t-shape-adjunctions-are-aspherical]
---

1. **Degree.** The degree map `d : G * <t> -> Z` is a homomorphism, so
   `d(u^k) = k d(u)`.
2. **Factoring.** `u^k in <<u>>`, so `<<u^k>> <= <<u>>`, and the identity of
   `G * <t>` induces a surjection `pi : G_w -> G_u` with `pi o q_w = q_u`. So
   `ker(q_w) <= ker(q_u)`, and injectivity of `q_u` gives injectivity of `q_w`.
3. **Corollary.** By item 1 of
   `torsion-free-amenable-t-shape-adjunctions-are-aspherical`, `q_u` is
   injective when `G` is torsion-free and `u` is cyclically reduced with amenable
   `t`-shape. Item 2 then applies.
4. **The shape of `u^k`.** Write `u` cyclically reduced in the normal form of
   `G * <t>`. Then no cancellation happens at the junction between the last
   syllable of `u` and the first, so the junctions between consecutive copies in
   `u^k` do not cancel either. Hence `u^k` is cyclically reduced, and its
   `t`-letter sequence is `k` copies of that of `u`: the cyclic word `S^k`.
   Non-amenability for `k >= 2` is the verbatim Forester--Rourke statement pinned
   in the claim. It is also checked exhaustively for shapes of length at most 10
   by the census script in `research/artifacts/kl-nonamenable-shapes-2026-09-13/`.
