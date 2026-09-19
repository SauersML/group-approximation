---
rg: 2
id: surface-generalized-bs-groups-satisfy-boone-higman
kind: claim
title: Every generalized Baumslag–Solitar group over a closed hyperbolic surface group, in particular every surface-by-(virtually free) group, embeds in a simple group of type F_∞
distinct_from:
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that covers graphs of groups over Z and over free groups; this covers graphs of groups over one-ended surface groups.
  hyperbolic-groups-satisfy-boone-higman: that covers hyperbolic inputs, such as surface-by-free groups with convex cocompact monodromy; this covers every surface-by-free group and every graph of surface groups over finite-index subgroups, hyperbolic or not.
  punctured-surface-mcgs-satisfy-permutational-boone-higman: that covers mapping class groups of punctured surfaces, which contain surface-by-free groups with injective monodromy; this needs no monodromy hypothesis and also covers graphs of surface groups (HNN extensions and amalgams over finite-index subgroups) that carry no monodromy structure at all.
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

**ESTABLISHED** (lane proof, not reviewed; route
`surface-generalized-bs-groups-satisfy-boone-higman-proof`). No priority claimed.

Let `G` be the fundamental group of a closed surface with negative Euler characteristic. Every group
in `BS_G` embeds in a simple group of type `F_∞`, and so satisfies `boone-higman-conjecture`. Here
`BS_G` is the class of fundamental groups of finite graphs of groups whose vertex and edge groups are
abstractly commensurable with `G`, with finite-index edge inclusions. This includes:

1. **Surface-by-(virtually free) groups.** Every extension `1 -> π_1(Σ) -> E -> Q -> 1` with `Σ`
   closed, `χ(Σ) < 0`, and `Q` finitely generated virtually free. In particular this covers every
   surface-by-free group `π_1(Σ) ⋊ F_m`, whatever the monodromy `F_m -> Aut(π_1 Σ)`, and every
   surface-by-cyclic group.
2. **Surface Baumslag–Solitar groups.** Every HNN extension `⟨π_1(Σ), t | t c t^-1 = ψ(c), c ∈ C⟩`
   with `C, ψ(C)` of finite index and `ψ` any isomorphism. (Whether some of these fail to be
   residually finite, like `BS(2,3)` over `Z`, is not decided here.)
3. **Amalgams and finite graphs.** Every amalgam or finite graph of (virtually) surface groups
   glued along finite-index subgroups.

It also applies verbatim to any `G` commensurable with a cocompact Fuchsian group.
