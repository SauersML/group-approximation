---
rg: 2
id: classwide-hyperbolic-kazhdan-hs-stability-proof
kind: route
title: Belegradek--Osin cover over a hyperbolic Kazhdan source, then transport stability to the quotient
target: classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan
requires: [belegradek-osin-rips-construction, torsion-free-hyperbolic-kazhdan-partner-exists, flexible-hs-stability-passes-to-kazhdan-kernel-quotients, flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear]
---

## Direct proof

Let `Q` be finitely presented with property (T).

1. `torsion-free-hyperbolic-kazhdan-partner-exists` gives a non-elementary
   hyperbolic group `H` with property (T).
2. `belegradek-osin-rips-construction` gives an exact sequence
   `1 -> N -> G -> Q -> 1` with `G` hyperbolic and `N` a quotient of `H`.
3. Property (T) passes to quotients, so `N` has (T). Property (T) is closed under
   extensions, so `G` has (T).
4. By hypothesis `G` is flexibly HS stable. Then
   `flexible-hs-stability-passes-to-kazhdan-kernel-quotients` makes `Q` flexibly HS
   stable.
5. Both listed consequences follow by applying
   `flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear` to `G -> Q`. ∎
