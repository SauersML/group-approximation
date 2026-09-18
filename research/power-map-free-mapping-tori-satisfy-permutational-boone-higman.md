---
rg: 2
id: power-map-free-mapping-tori-satisfy-permutational-boone-higman
kind: claim
title: Ascending HNN extensions of F_n along permuted power maps x_i -> x_π(i)^(m_i) lie in the permutational Boone--Higman class
distinct_from:
  pbh-class-closed-under-relative-holomorphs: that is the general permanence statement for partial-conjugation mapping tori over any finitely generated member of the class; this specializes it to power-map endomorphisms of free groups, through a finite-index passage and an explicit affine model.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that covers Baumslag--Solitar groups and free-by-cyclic groups, where the endomorphism is surjective or the base is cyclic; this covers non-surjective power maps of F_n with n >= 2, whose natural Bass--Serre trees are not locally finite.
  one-relator-groups-satisfy-boone-higman: that is the open problem for all one-relator groups; this settles one family of ascending HNN extensions of free groups, which contains the Druţu--Sapir group.
  drutu-sapir-group-satisfies-boone-higman: that is the plain Boone--Higman statement for one group; this is the permutational statement for a family containing it.
---

**ESTABLISHED** through `power-map-free-mapping-tori-pbh-proof`. Not
independently reviewed. No priority is claimed.

## Statement

Let `n >= 1`, `π ∈ S_n`, and let `m_1, ..., m_n` be nonzero integers. Let
`φ : F_n -> F_n` be the endomorphism `φ(x_i) = x_π(i)^(m_i)`. It is injective,
because the images are nonzero powers of the `n` distinct basis letters. Then

    G_φ = < x_1, ..., x_n, t | t x_i t^-1 = x_π(i)^(m_i)  (1 <= i <= n) >

lies in `B_A`, the class of groups embedding in a group admitting an action of
type (A). By `type-a-action-gives-boone-higman-for-subgroups`, `G_φ` has
solvable word problem and embeds in a finitely presented simple group.

## Members

- **Cyclic base:** `n = 1` gives `BS(1, m_1)`, already known.
- **The Druţu--Sapir group:** `n = 2`, `π = (1 2)`, `(m_1, m_2) = (2, 1)`. This is
  `DS = <a, b | a^2 b^2 a^-2 b^-1>`, through the ascending HNN form (DS0) of
  `drutu-sapir-group-index-two-squaring-mapping-torus` with `t = a^-1`. It is
  residually finite, not linear, not hyperbolic and not virtually
  free-by-cyclic. See `drutu-sapir-group-satisfies-boone-higman`.
- **Its index-two subgroup:** `K = <x, y, t | t x t^-1 = x^2, t y t^-1 = y^2>`,
  that is `BS(1,2) *_<t> BS(1,2)`.
- **All exponents ±1:** `φ` is an automorphism of finite order, so `G_φ` is
  virtually `F_n × Z`.

## What this does not reach

- **Other endomorphisms.** General injective endomorphisms of `F_n` stay open
  here. `pbh-class-closed-under-relative-holomorphs` reaches `F_n *_φ`
  whenever some finite-index subgroup of the mapping torus is isomorphic to `J *_β`
  as in its part (T). For example it also gives
  `< x, y, t | t x t^-1 = x^2, t y t^-1 = y x >`. It is not decided whether every
  injective endomorphism is realized in this way. A test case not settled here is
  `φ(x) = x y`, `φ(y) = y x`.
- **Other Magnus steps.** HNN steps over non-free bases are not reached, for
  example the Baumslag--Gersten group
  (`baumslag-gersten-group-satisfies-boone-higman`).

## Why the natural routes failed and this one works

- **Trees.** The Bass--Serre tree of `G_φ` is not locally finite when some
  `|m_i| >= 2` and `n >= 2`, so Bux--Llosa Isenrich--Wu do not apply as stated
  (Attempt 1 of `drutu-sapir-group-satisfies-boone-higman`).
- **Linear hosts.** `DS` is not linear.
- **Relative automorphisms.** What works is that the squaring step `t` is realized
  as conjugation by `σ` inside `BS(1,2)`. The free product structure comes from a
  free letter. The two sit together in
  `Aut_B(B * F_2)`, which lies in `B_A` by
  `pbh-passes-to-relative-free-group-automorphisms`.

## Update (bh-free-05, 2026-09-18)

General injective endomorphisms are now covered by `ascending-hnn-of-free-groups-satisfy-boone-higman` (b6bb206cf, lane proof, not reviewed). Every ascending HNN extension F*_φ of a finitely generated free group embeds in a member of BS_{F_2}, through M. Hall's theorem on F * Z, and so it satisfies BH and lies in `B_A` by BLIW §12.5. In particular the test case `φ(x) = x y`, `φ(y) = y x` named above is settled. This node's power-map argument is an independent, more explicit route for its own family.
