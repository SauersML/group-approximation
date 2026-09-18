---
rg: 2
id: baumslag-gersten-group-is-highly-transitive-and-mif
kind: claim
title: The Baumslag--Gersten group is acylindrically hyperbolic, highly transitive and mixed-identity-free, yet every faithful action of it with finitely many orbits of two-element subsets has an infinitely generated point stabilizer
requires:
  - fpbs-minasyan-osin-weakly-malnormal-splittings
  - type-a-actors-split-only-over-orbit-finite-edges
distinct_from:
  type-a-actors-have-no-proper-power-cyclic-edge-splittings: that proves BG has no action of type (A); this shows that of the clauses of type (A), only finite generation of point stabilizers fails, since BG does have faithful highly transitive actions.
  baumslag-gersten-group-satisfies-boone-higman: that is the open embedding question for BG; this is a structural fact about BG itself, used there to locate the obstruction.
---

**ESTABLISHED** (lane proof from imported theorems read at source; not reviewed; no
priority claimed, likely folklore). Let `BG = < a, t | b a b^-1 = a^2 >` with `b = t a t^-1`.

## Statement

1. `BG` is acylindrically hyperbolic.
2. `BG` is torsion-free, so its finite radical is trivial. Hence `BG` is highly transitive
   (it has a faithful highly transitive action on a countable set) and mixed-identity-free
   (MIF).
3. Every faithful action of `BG` on a set with finitely many orbits of two-element subsets,
   for example every highly transitive one, has a point stabilizer that is not finitely
   generated.

## Proof

1. `BG` is the HNN extension of `A = BS(1,2) = < a, b | b a b^-1 = a^2 >` with associated
   subgroups `C = <a>` and `D = <b>` and stable letter `t` (`t a t^-1 = b`); eliminating `b`
   gives the one-relator presentation. `C != A != D`, since `A` is not cyclic. The subgroup
   `C` is weakly malnormal in `BG`: for `g = t^-1`, `C^g = t C t^-1 = D`, and `C ∩ D = 1` in
   `A`, because `<a>` lies in the kernel of the exponent map `A → Z`, `b ↦ 1`, which `<b>`
   meets trivially. Minasyan--Osin's HNN corollary (`fpbs-minasyan-osin-weakly-malnormal-splittings`,
   item 2) makes `BG` acylindrically hyperbolic.
2. The relator `t a t^-1 a t a^-1 t^-1 a^-2` has `a`-exponent sum `-1`. A proper power `w^k`,
   `k >= 2`, has exponent sums divisible by `k`, so the relator is not a proper power, and the
   one-relator group `BG` is torsion-free (Karrass--Magnus--Solitar). Its finite radical
   `K(BG)` is therefore trivial. Hull--Osin, arXiv:1501.04182, read at source:
   - Theorem (TeX label `main`): "every countable acylindrically hyperbolic group with trivial
     finite radical is highly transitive";
   - Corollary (TeX label `ah-mif`): "Let `G` be an acylindrically hyperbolic group. Then
     `G/K(G)` is MIF. In particular, if `K(G) = {1}`, then `G` is MIF".

   Their one-relator corollary (TeX label `1-rel`) needs at least 3 generators, and `BG` has
   2, so it does not apply; the HNN splitting of step 1 replaces it.
3. This is instance 3 of `type-a-actors-have-no-proper-power-cyclic-edge-splittings-proof`,
   which uses only `type-a-actors-split-only-over-orbit-finite-edges`. Suppose `BG` acts
   faithfully on `X` with finitely generated point stabilizers and finitely many orbits of
   two-element subsets. The Bass--Serre tree of step 1 is irreducible, so the edge group
   `<a>` has finitely many orbits on `X`. Let `r(c)` count the infinite `<c>`-orbits; it is
   conjugation invariant and `r(c^2) = 2 r(c)`. Since `a ~ a^2`, `r(a) = 0`, so `X` is a
   finite union of finite orbits, and the infinite group `BG` cannot act faithfully on it.
   A highly transitive action is transitive on two-element subsets, so it is covered. ∎

## What it changes

By BFFHZ Theorem C (`fp-simple-highly-transitive-groups-satisfy-pbh`), `BG` satisfies PBH
exactly when it embeds in a finitely presented simple MIF group. `BG` is finitely presented
and MIF but not simple. So the hypotheses of BFFHZ's Theorem E (a finitely presented simple
MIF group `G` makes `Aut_G(G*F_n)` a type (A) actor on `Hom_G(G*F_n, G)`) fail for `BG` only
through simplicity. That hypothesis cannot be dropped. `Hom_G(G*F_n, G) = G^n` via the images
`g_i` of the free generators `x_i`, and the pair invariant `(φ, ψ) ↦ ψ(ker φ)` is
`Aut_G(G*F_n)`-invariant and symmetric, and equals `<<h_1 g_1^-1, …, h_n g_n^-1>>`. So it
takes every value `<<k_1, …, k_n>>` in `G`. For `G = BG`, the normal closures `<<t^m>>`,
`m >= 0`, are pairwise distinct (their images in `BG^ab = Z` are `mZ`), so there are
infinitely many orbits of two-element subsets. So for `BG` the conclusion of the BFFHZ
proposition with TeX label `prop:2trans` (high transitivity; read at source) fails; its proof
uses simplicity of `G` throughout.
