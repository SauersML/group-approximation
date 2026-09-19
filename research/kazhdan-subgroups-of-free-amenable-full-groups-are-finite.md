---
rg: 2
id: kazhdan-subgroups-of-free-amenable-full-groups-are-finite
kind: claim
title: "If an amenable group acts continuously and essentially freely on a compact metrizable space with an invariant measure of full support, every Kazhdan subgroup of the topological full group is finite"
distinct_from:
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that gives almost every orbit finite, hence residual finiteness and no infinite simple Kazhdan subgroup; this upgrades the topological case to finiteness, which also excludes residually finite Kazhdan groups such as SL_3(Z) and Z^3 ⋊ SL_3(Z).
  elek-monod-near-hit-has-torsion-no-kazhdan-subgroup: that excludes infinite Kazhdan subgroups of one Z^2 full group through a wobbling theorem needing subexponential growth; this holds for every amenable acting group with an invariant measure of full support and essentially free action.
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that host contains Z^3 ⋊ SL_3(Z) because its acting group is non-amenable and it has no invariant measure; this shows that both features are needed among transformation groupoids of amenable groups.
---

**ESTABLISHED** by `kazhdan-subgroups-of-free-amenable-full-groups-are-finite-proof`.

## Statement

Let `P` be a countable amenable group acting continuously on a compact metrizable space
`X`. Let `μ` be a `P`-invariant Borel probability measure of full support such that
`μ`-almost every point has trivial stabiliser. Then every subgroup `K` of the topological
full group `[[P ⋉ X]]` with property (T) is finite. Moreover its orbits on `X` are bounded
by the constant `M` of `kazhdan-orbit-bound-in-amenable-by-free-groups`.

Here `[[P ⋉ X]]` is as in `dense-finite-free-orbits-force-finite-kazhdan-subgroups`: the
homeomorphisms `g` with `g(x) = c_g(x)·x` for a continuous `c_g : X → P`.

## Consequences

1. **Free minimal actions.** If `P` is amenable and acts freely and minimally on a compact
   metrizable `X`, every Kazhdan subgroup of `[[P ⋉ X]]` is finite. An invariant
   probability measure exists by amenability, and its support is closed, invariant and
   nonempty, hence all of `X` by minimality. In particular this holds for `[[Z^2 ⋉ Ω]]`,
   `Ω` a free minimal `Z^2`-SFT: the `Z^2` factor of every host in
   `decidable-algebras-embed-in-z2-sft-boundary-product-hosts`.
2. **Class kill: permutational hosting of Kazhdan inputs over amenable acting groups.**
   A route that embeds a group containing an infinite Kazhdan subgroup into
   `[[P ⋉ X]]` fails for every such `(P, X, μ)`. Examples of such groups are `SL_3(Z)`,
   `Z^3 ⋊ SL_3(Z)` and the decidable simple Kazhdan hosts of
   `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`. It also covers routes through
   the copy `g ↦ Σ_p u_p 1_{c_g^{-1}(p)}` of `[[P ⋉ X]]` inside the unit group of
   `LC(X, F_2) ⋊ P`. It does not cover the Leavitt-tensor hosts of
   `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units`, whose acting groups
   are not amenable. The invariant
   is property (T). Every member dies at Step 2 of the proof: the invariant measure makes
   almost every orbit finite, and the uniform bound turns that into finiteness.
3. **Sharpness.** Each hypothesis is needed, since dropping it admits an infinite Kazhdan
   subgroup:
   - *amenability of `P`*: `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`,
     and trivially `P = Γ` Kazhdan acting freely;
   - *the invariant measure, with a non-amenable acting group*: the Robertson–Steger
     boundary action in `af-by-z2-ample-groupoid-full-group-contains-infinite-kazhdan`.
   With `P = Z^2 × F_d` on `Ω × ∂F_d` there is no invariant probability measure, since
   `F_d` has none on `∂F_d`. That case is reduced to orbit finiteness on free points by
   `dense-finite-free-orbits-force-finite-kazhdan-subgroups`.

## Prior art

The almost-everywhere part is classical (Connes–Weiss, Schmidt; see the credit paragraph
of `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`). The case `d = 0` of the
orbit bound is the folklore statement that Kazhdan expanders do not inject Lipschitz into
amenable groups at unbounded size. No reference stating the finiteness theorem was found
in a short search. Novelty is not claimed.

DERIVATION
kazhdan-subgroups-of-free-amenable-full-groups-are-finite-proof
