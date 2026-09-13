---
rg: 2
id: braid-group-b4-has-the-haagerup-property
kind: claim
title: The braid group B_4 has the Haagerup property
distinct_from:
  braid-group-b4-lacks-the-haagerup-property: that claim is the negation of this one
  every-braid-group-has-the-haagerup-property: that claim is the property for all n; this is the smallest undecided case, necessary for it but not sufficient
---

`B_4` admits a proper conditionally negative definite function.

Equivalent forms (`braid-haagerup-iff-punctured-sphere-mcg-haagerup`,
`braid-haagerup-induction-reduces-to-brunnian-braids`, and §2 of
`research/artifacts/zp-braid-haagerup-b4-attacks-2026-09-13-part3.md`):

- `Mod(S_{0,5})`, equivalently `PMod(S_{0,5}) ≅ F_3 ⋊ F_2` (point pushing), has the Haagerup property;
- `P_4` admits a cnd function whose restriction to the free normal subgroup of Brunnian braids `Brun_4` is proper;
- the preimage `F_2 ⋊ Λ` in `B_4/Z(B_4)` of a torsion-free finite-index `Λ ≤ SL_2(Z)` has it. Assuming the outer
  action is the natural one (Dyer–Formanek–Grossman; not re-verified), this is the fundamental group of the
  universal punctured elliptic curve over the open modular curve. With the zero section kept it would be the
  Burger pair `Z^2 ⋊ Λ`, which fails the property.

## Attempts

- **Products of trees** from the five forgetful maps `PMod(S_{0,5}) → F_2`: proper exactly modulo the Brunnian
  loops, which are free of infinite rank. Stops there (§3 of the artifact).
- **Complex hyperbolic monodromy** (Thurston, Deligne–Mostow) gives cnd functions `d(o, ρ_α(g) o)`. For finitely
  many lattice parameters the joint kernel meets `Brun_4` in an infinite subgroup (twist powers). An infinite
  weighted family is open and needs uniform growth estimates along `Brun_4` (§4).
- **Cubulation through the Sanov subgroup**: the preimage is an amalgam over the fiber `F_2` of two
  graph-manifold groups, which are cubulated. The normal edge group blocks combination theorems, and the natural
  torus walls are not invariant under both monodromies (§5).
- **Open next step:** build a cnd function on `P_4` proper on `Brun_4`, for example from actions of `P_4` on
  median spaces built from arcs between punctures, or show no such function exists (see
  `braid-group-b4-lacks-the-haagerup-property`).
