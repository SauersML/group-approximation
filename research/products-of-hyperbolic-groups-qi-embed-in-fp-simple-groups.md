---
rg: 2
id: products-of-hyperbolic-groups-qi-embed-in-fp-simple-groups
kind: claim
title: Groups undistorted in type (A) actors are closed under finite direct products and finite-index overgroups, so every finite product of hyperbolic groups and copies of Aut(F_n) quasi-isometrically embeds in a finitely presented simple group
distinct_from:
  hyperbolic-groups-lie-in-the-permutational-class: that puts finite direct products of hyperbolic groups into finitely presented simple groups as abstract embeddings; this makes those embeddings quasi-isometric.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure of the permutational class under products and finite-index overgroups; this is the same closure for the undistorted version of the class.
  hyperbolic-groups-undistortedly-embed-in-fp-simple-groups: that is one hyperbolic group; this is finite products of them, mixed with Aut(F_n) factors, and their finite-index overgroups.
  virtually-compact-special-groups-undistorted-in-2v: that gives an F_infinity host, but only for virtually compact special factors; this allows every hyperbolic factor, with a host that is only known to be finitely presented.
---

**ESTABLISHED** by `qi-permutational-class-products-and-finite-extensions-proof` (lane proof, formal on top
of landed nodes, not independently reviewed; no priority claimed).

Call a finitely generated group `G` **QI-permutational** if it is isomorphic to an undistorted subgroup of
a finitely generated group `Δ` with an action of type (A), in the sense of
`type-a-action-gives-boone-higman-for-subgroups`.

1. **Payoff.** A QI-permutational `G` quasi-isometrically embeds in the finitely presented simple
   twisted Brin–Thompson group `SV_Δ`.
2. **Closure.** The class is closed under undistorted finitely generated subgroups, finite direct
   products, and finite-index overgroups.
3. **Inputs.**
   - Every hyperbolic group is QI-permutational, through `Δ = [[G*Z | ∂_h(G*Z)]]`.
   - Every `Aut(F_n)` is QI-permutational, through the BFFHZ group `Δ = Aut_V(V * F_n)`, of which it is a
     retract.
4. **Consequence.** Let a finitely generated group have a finite-index subgroup that is undistorted in
   `H_1 × ⋯ × H_k`, where each `H_i` is hyperbolic or some `Aut(F_n)`. Then it quasi-isometrically embeds
   in a finitely presented simple group. Examples:
   - finite direct products of hyperbolic groups, including non-cubulated ones such as Kazhdan hyperbolic
     groups;
   - `H × Aut(F_n)` with `H` hyperbolic.

This is the "(quasi-isometrically?)" half of Zaremsky's question (arXiv:2201.00711v1, TeX l.495–497) for
these products. The type F_∞ half is not addressed. For virtually compact special factors it holds with
the host `2V` (`virtually-compact-special-groups-undistorted-in-2v`).
