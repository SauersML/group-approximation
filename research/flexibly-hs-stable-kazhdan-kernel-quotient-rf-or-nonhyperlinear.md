---
rg: 2
id: flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear
kind: claim
title: A quotient of a flexibly HS-stable group by a Kazhdan normal subgroup is residually finite or non-hyperlinear
distinct_from:
  flexible-hs-stability-passes-to-kazhdan-kernel-quotients: that transports flexible HS stability to the quotient; this combines it with Malcev residual finiteness and names the dichotomy that consumers use.
  kac-moody-lattice-is-non-hyperlinear-or-llp-failure: that is a dichotomy about one simple Kazhdan lattice itself; this is a dichotomy about every Kazhdan-kernel quotient of a stable group, and through a Belegradek--Osin cover it reaches such lattices from a hyperbolic group.
  leavitt-unit-hs-stable-iff-nonhyperlinear: that is the stability equivalence for the Leavitt unit group itself; this transfers stability from any group mapping onto it with a Kazhdan kernel, such as its hyperbolic Kazhdan cover.
---

**ESTABLISHED.** Let `Γ` be finitely generated and flexibly Hilbert--Schmidt
stable, and let `N ◁ Γ` have property (T). Then `Γ/N` is residually finite or
not hyperlinear. In particular, if `Γ/N` is infinite and minimally almost
periodic, then `Γ/N` is not hyperlinear.

**Instances.**

- **The Leavitt unit group.** `hyperbolic-kazhdan-cover-of-leavitt-unit-group` gives a hyperbolic Kazhdan group `G` with a Kazhdan kernel `N` and `G/N ≅ L_(F_2)(1,2)^×`. That quotient is infinite and minimally almost periodic (`binary-leavitt-unit-group-is-minimally-almost-periodic`). So if `G` is flexibly HS stable, the binary Leavitt unit group is not hyperlinear.
- **Simple Kac--Moody lattices.** Let `Λ` be a finitely presented Caprace--Rémy simple Kazhdan lattice. A Belegradek--Osin cover of `Λ` over a hyperbolic Kazhdan source is a hyperbolic Kazhdan group with a Kazhdan kernel. So if that cover is flexibly HS stable, `Λ` is not hyperlinear.

Neither instance is a cheaper route to `non-hyperlinear-group` than proving the
quotient itself stable, because stability of the cover implies stability of the
quotient.

DERIVATION
kazhdan-kernel-quotient-rf-or-nonhyperlinear-proof
