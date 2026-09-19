---
rg: 2
id: fibred-v-towers-in-brin-thompson-groups-are-distortion-free
kind: claim
title: The fibred towers T_1 = V, T_(j+1) = C(C,T_j) ⋊ V inside (j+1)V, and everything built from V by subgroups, products and continuous wreaths, are distortion-free, so they contain no H_3(Z), no BS(1,k) and no Callard–Salo element
distinct_from:
  cantor-maps-by-v-embed-in-next-brin-thompson-group: that is the embedding C(C,Γ) ⋊ V ≤ (n+1)V; this proves that iterating it from V never produces a distorted element.
  heisenberg-group-embeds-in-some-brin-thompson-group: that is the open existence question; this kills the whole fibring class of constructions for it.
  coordinate-shadows-rigidify-abelian-normalizers-in-nv: that kills Heisenberg and Sol extensions of block-split Z^d by a projection invariant; this kills every distorted element, over any Z^d or none, in the fibred-tower class, by a word-length invariant.
  heisenberg-not-in-full-groups-of-z4-actions: that kills wobbling and full-group hosts of rank at most 4 by growth; this kills a different host class, which has exponential growth and arbitrary depth.
  brin-thompson-mv-contains-a-distortion-element: that gives a distorted element in every mV with m >= 2; this shows that such an element lies outside every fibred tower.
---

**ESTABLISHED** by `fibred-v-towers-distortion-free-proof`, a lane proof dated 2026-09-19
(swarm-0917-w17-w17-z-break). It has not been independently reviewed.

**Definitions.**
- Let `𝒯` be the smallest class of groups with these properties:
  - it contains every subgroup of Thompson's `V`;
  - it is closed under subgroups and finite direct products;
  - it is closed under continuous wreaths `C(X,Γ) ⋊ W` with `Γ, W ∈ 𝒯` and `X` any compact
    `W`-space.
- The fibred towers are `T_1 = V` and `T_{j+1} = C(C, T_j) ⋊ V`, with `V` acting on `C = {0,1}^N`.
  By `cantor-maps-by-v-embed-in-next-brin-thompson-group`, `T_j ≤ jV`.

**Theorem.** Every group in `𝒯` is distortion-free, in the sense of
`cantor-wreath-distortion-descends-to-fibre-or-base`. Hence no group in `𝒯` contains any of:
1. `H_3(Z)`, or any finitely generated torsion-free nilpotent group that is not abelian;
2. `BS(1,k)` with `|k| ≥ 2`;
3. an element `f` with `|f^N| = o(N)`, such as the Callard–Salo element of
   `brin-thompson-mv-contains-a-distortion-element`.

In particular `T_j ≠ jV` for `j ≥ 2`. This holds for every conjugate of `T_j` and every
subgroup, so the Callard–Salo element lies in no conjugate of any `T_j`.

**What this kills.**
- **Class.** Constructions of `H_3(Z)` or `BS(1,2)` inside some `mV` that only:
  - start from subgroups of `V`;
  - take products;
  - fibre a group over a Cantor coordinate by locally constant maps twisted by a base action.
  This is the compiler of `cantor-maps-by-v-embed-in-next-brin-thompson-group`, iterated to any
  depth. It also covers Kaloujnine–Krasner-type cocycle realizations over a compact base.
- **Invariant.** Linear growth of `|g^N|`.
- **Where every member dies.**
  - Suppose some power of the central commutator `c` has trivial base image. That power is a pure
    fibre map `(h,1)`. By Step 3 of the proof route, its value `h(x_0)` at a point of infinite
    order is quadratically distorted in a finitely generated subgroup of the fibre.
  - Otherwise the base image of `c` itself is quadratically distorted.
  - Either way the distortion descends one level. After finitely many levels it reaches a subgroup
    of `V`, which contradicts `thompson-v-cyclic-subgroups-are-undistorted`.
- **Forced shape of a survivor.**
  - Every `H_3(Z) ≤ mV`, and every `BS(1,2) ≤ mV`, uses elements that do not lie in any group of
    `𝒯` embedded in `mV`. For example, Callard–Salo's reversible-Turing-machine elements
    genuinely mix coordinates.
  - More sharply, by Corollary 2 of the transfer claim, `H_3 ≤ C(X,Γ) ⋊ W` forces a
    `√`-distorted element in `Γ` or in `W`. So fibring never creates the first Heisenberg group
    in a tower. It can only carry one up from a fibre or a base that already has a
    square-root-distorted element.

**Remark, not part of the established statement.** A Sol lattice `Z^2 ⋊_A Z` with `A` hyperbolic
has an exponentially distorted `Z^2`, by the standard base-`λ` expansion argument, which is not
re-derived here. If that is granted, item 3 also excludes from `𝒯` every Sol lattice and every
Burger pair `Z^2 ⋊ Γ` whose `Γ` contains a hyperbolic matrix. Those are the relative-(T)
witnesses sought in `brin-thompson-2v-is-not-a-t-menable`.
