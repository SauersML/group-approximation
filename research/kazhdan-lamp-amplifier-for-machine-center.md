---
rg: 2
id: kazhdan-lamp-amplifier-for-machine-center
kind: claim
title: A finitely presented Kazhdan-lamp amplifier for the switchable machine center
distinct_from:
  sofic-safe-finite-presentation-compiler: that asks to make the Mikhailova Higman rope sofic; this asks for a Higman-free finite presentation whose nonsofic branch is a Kun--Thom coset wreath with coefficients in the machine center.
  machine-center-vanishes-exactly-on-inf: that supplies the switchable central coefficient group; this is the missing finite-presentation amplifier that would consume it.
---

OPEN.  Let `Gamma <= G` be a finitely presented infranormal non-normal pair
of Kazhdan groups.  Let `G_e`, `Phi_e` be as in
[[machine-center-vanishes-exactly-on-inf]]: `Phi_e`
is central, trivial on `INF`, nontrivial on `FIN`.  Wanted: finitely
presented groups `K_e`, computable from `e`, with

```text
e in INF  ==>  K_e sofic,
e in FIN  ==>  K_e contains  Phi_e wr_(G/Gamma) G = (directSum_(G/Gamma) Phi_e) x| G.
```

The abstract target is `G_e x (Phi_e wr_(G/Gamma) G)`.  It is `G_e x G` on
`INF` and contains the nonsofic coset wreath on `FIN`, so the polarities are
right.  On `FIN` it is not finitely generated, so `K_e` must be a finitely
presented overgroup whose relations generate the lamps.

With the upper bound this proves
[[sofic-recognition-finite-presentations-is-pi2-complete]] with no Higman
compiler.

## Attempts

1. **Tensor lamps on the whole abelian normal subgroup `T_e`.**  Nonsofic for
   every `e`: partial configuration coordinates are nonzero on `INF` too, and
   each spans a coset wreath.
2. **Lamps on full coordinates only.**  Completing a partial word with its last
   `A`-letter does not commute with `G`, so the module is not invariant.  The
   quotient that kills `G` on partial coordinates leaks into the full ones and
   kills the `FIN` lamps.
3. **Central product of coset copies of `G_e` modulo `Phi_e`.**  Abstractly it
   is `G_e x (Phi_e wr_(G/Gamma) G)`.  The machine letters, which manufacture
   configuration words, act trivially on `Phi_e`.  So a finitely presented
   overgroup must obtain the lamp coordinate at `Gamma` from a machine module
   with partial coordinates, and removing their `G`-translates needs
   infinitely many identification relations.  This is the Cornulier
   double-coset obstruction for permutational wreath products (Geom. Dedicata
   122 (2006)); no infranormal non-normal Kazhdan pair with finitely many double cosets is
   known here.
4. **Twisted doubles `G *_Gamma G` by a `Phi_e`-valued central cocycle.**  Wrong
   polarity: on `INF` the twist vanishes and the untwisted double is nonsofic.

Full analysis: `research/artifacts/sofic-fp-machine-center-amplifier-2026-09-12.md`.
