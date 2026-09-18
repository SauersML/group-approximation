---
rg: 2
id: virtually-compact-special-groups-undistorted-in-2v
kind: claim
title: Every virtually compact special group, in particular every cubulated hyperbolic group, quasi-isometrically embeds in the simple group 2V of type F_infinity
distinct_from:
  virtually-special-groups-embed-in-brin-thompson-group-2v: that embeds every group virtually inside a finitely generated right-angled Artin group into 2V; this shows that the same embedding is quasi-isometric when the finite-index subgroup is undistorted in the right-angled Artin group, as it is for compact special cube complexes.
  hyperbolic-groups-undistortedly-embed-in-fp-simple-groups: that gives every hyperbolic group an undistorted embedding into a finitely presented simple host not known to be F_infinity; this gives the cubulated ones an undistorted embedding into 2V, which is F_infinity, so both of Zaremsky's refinements hold for them.
  raags-are-undistorted-in-brin-thompson-group-2v: that is the right-angled Artin case; this passes to finite-index overgroups of undistorted subgroups.
---

**ESTABLISHED** by `virtually-compact-special-undistorted-in-2v-proof` (lane proof, not independently
reviewed; no priority claimed, bounded search).

## Statement

1. Let `G` be finitely generated with a finite-index subgroup `H` that is isomorphic to an undistorted
   subgroup of a finitely generated right-angled Artin group. Then `G` has a quasi-isometric embedding
   into `2V`, the embedding of `virtually-special-groups-embed-in-brin-thompson-group-2v`.
2. This applies when `G` is **virtually compact special**, i.e. some finite-index subgroup is `π_1 X`
   for a compact special cube complex `X`.
3. In particular it applies to every hyperbolic group acting properly and cocompactly on a CAT(0) cube
   complex (Agol, `cubulated-hyperbolic-groups-are-virtually-special`).

`2V` is simple (Brin) and of type F_∞ (Kochloukova–Martínez-Pérez–Nucinkis), as recalled in
Belk–Zaremsky, arXiv:2001.04579, TeX l.151 and l.185.

## What this answers

Zaremsky, arXiv:2201.00711v1, TeX l.495–497 (node `hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups`):

> Do each of the following groups embed (quasi-isometrically?) into a finitely presented simple group
> (even of type F_∞?) Braid groups, mapping class groups, Out(F_n), CAT(0) groups, hyperbolic groups.

- **Hyperbolic groups.** Every cubulated hyperbolic group gets a yes to both refinements at once, with
  one host `2V` for all of them. Examples are free groups and closed surface groups. What stays open is
  the hyperbolic groups that are not virtually compact special. By Agol these are exactly the
  non-cubulated ones (a finite-index subgroup acting geometrically on a CAT(0) cube complex induces a geometric action of `G` on a product of copies of it), for example infinite hyperbolic groups with property (T), such as cocompact
  lattices in `Sp(n,1)`.
- **CAT(0) groups.** Both refinements hold for fundamental groups of compact special cube complexes, which
  are CAT(0) groups. Among them are finitely generated right-angled Artin groups. The class is closed
  under finite direct products, because `A_Γ × A_Λ = A_{Γ*Λ}` (join) and undistortion passes to products.
- **Low-complexity cases of the other items.**
  - `B_3` contains `B_3' × Z(B_3) ≅ F_2 × Z`, a right-angled Artin group, with index 6.
  - `Out(F_2) ≅ GL_2(Z)` and the torus mapping class group `SL_2(Z)` are virtually free.
  - So all three quasi-isometrically embed in `2V`.
  - Nothing is claimed for `B_n` with `n >= 4`, higher-genus mapping class groups, or `Out(F_n)` with
    `n >= 3`.

## Scope

- The embedding is the one already on main. What is new is the undistortion, and above all the fact
  that the host is F_∞ and simple, which the BBMZ host `SV_Γ` is not known to be.
- Virtually compact special groups are virtually CAT(0). Finite extensions of CAT(0) groups need not be
  CAT(0), so item 2 is phrased for the class itself.
