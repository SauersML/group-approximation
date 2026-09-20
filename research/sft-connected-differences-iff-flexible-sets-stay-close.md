---
rg: 2
id: sft-connected-differences-iff-flexible-sets-stay-close
kind: claim
title: An SFT has coarsely connected difference sets exactly when no point can be changed independently on two far-apart regions; opposed half-plane pairs kill products
distinct_from:
  fp-v-times-subshift-full-groups-force-connected-differences: that proves coarse connectivity is necessary for finite presentation of the V-product full group; this is an exact reformulation of coarse connectivity itself for SFTs, with no group attached, plus a product criterion.
  metallic-wang-shift-product-is-minimal-with-split-differences: that is one product of two Wang shifts with split differences; part 3 here is the general criterion (opposed half-plane pairs) of which the band pairs there are one instance.
  minimal-sfts-have-no-finite-asymptotic-pairs: that rules out finite flexible sets in minimal SFTs; this characterizes coarse connectivity through infinite flexible sets.
---

**ESTABLISHED.** Route: `sft-connected-differences-iff-flexible-sets-stay-close-proof`.

**Setting.**
- `Λ` is a finitely generated group with a word metric `d`. `X ⊆ A^Λ` is a subshift of finite
  type. Its allowed patterns are given on the windows `pB_r`, the balls of radius `r`.
- `Δ(x, y) = {p : x(p) ≠ y(p)}`. A set is *`m`-connected* if it cannot be split into two
  nonempty parts at distance `> m`. This is the notion of
  `fp-v-times-subshift-full-groups-force-connected-differences`.
- A point `x ∈ X` is *flexible on* `U ⊆ Λ` if some `y ∈ X` with `y ≠ x` agrees with `x` off `U`.

**Theorem.** Let `m >= 2r`.
1. **Characterization.** Every difference set of `X` is `m`-connected if and only if no
   `x ∈ X` is flexible on two sets `U_1`, `U_2` with `d(U_1, U_2) > m`.
2. **Gluing.** If `x` is flexible on `U_1` and on `U_2` with `d(U_1, U_2) > m`, then some
   `z ∈ X` has `Δ(x, z) = D_1 ⊔ D_2`, where each `D_i ⊆ U_i` is nonempty.
3. **Products over `Z^d`.** Say `X ⊆ A^(Z^d)` has an *`n`-half-space pair* (for `n ≠ 0`) if some
   `x ≠ y` in `X` agree on `{p : ⟨p, n⟩ >= 0}`. If `X` has an `n`-half-space pair and the SFT `Y`
   has a `(-n)`-half-space pair, then for every `m` the product `X × Y` has a difference set
   that is not `m`-connected.
   - In particular, for every infinite SFT `X ⊆ A^(Z^2)`, the product `X × X^rev` fails, where
     `X^rev = {p ↦ x(-p)}`. This uses the existence of a nonexpansive line
     (Boyle--Lind, *Expansive subdynamics*, Trans. AMS 349 (1997); quoted, not re-read here).

**Consequences.**
- *Checking a candidate host.* For an SFT host of the V-product route, the necessary condition of
  `fp-v-times-subshift-full-groups-force-connected-differences` is local. One exhibits a point
  and two regions far apart on which it can be changed. Nothing about pairs in general is needed.
- *Class kill for layered constructions.* Suppose a construction of hard minimal free SFTs
  (`minimal-free-z2-sfts-have-arbitrarily-hard-row-languages`) is taken as a direct product of
  two independent layers. If one layer has an `n`-half-space pair and the other a
  `(-n)`-half-space pair, the host fails P2, for any `n`.
  - The golden-silver kill (`v-times-golden-silver-wang-product-full-group-is-not-fp`) is the
    case `n = e_2`. There each band pair is a pair for both `n` and `-n`.
  - Only minimality of the product is specific to that example.
- *Scope.* The theorem says nothing about the synchronized, non-product layers of the
  Durand--Romashchenko lift itself. For that see
  `connected-difference-zd-sfts-are-a-e-half-space-determined`.
