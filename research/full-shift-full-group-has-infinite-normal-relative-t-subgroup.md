---
rg: 2
id: full-shift-full-group-has-infinite-normal-relative-t-subgroup
kind: claim
title: "Some subgroup of the full-shift topological full group has an infinite normal subgroup with relative property (T), necessarily locally finite, for instance a copy of EL_2(F_p[t,t^-1]) ⋉ F_p[t,t^-1]^2"
distinct_from:
  wobbling-normal-relative-t-subgroups-are-locally-finite: that proves any such normal subgroup is locally finite; this asks whether an infinite one exists at all
  full-shift-topological-full-group-is-a-t-menable: that is the Haagerup property of [[X]]; this claim, if true, refutes it, and its negation is only the normal-pair part of that property
  elementary-linear-semidir-pair-relative-t: that gives the relative-(T) pairs; this asks whether one with a locally finite base lives inside [[X]]
---

**OPEN.** `X = {0,1}^Z` and `[[X]]` its topological full group.

**Statement.** There are `Γ ≤ [[X]]` and an infinite `H ⊴ Γ` such that `(Γ, H)` has relative
property (T).

## Role

- If true, `[[X]]` is not Haagerup: a Haagerup group has no relative-(T) pair with an infinite
  subgroup. That refutes `full-shift-topological-full-group-is-a-t-menable`, and through
  `full-shift-full-group-a-t-menable-from-nv` it refutes `brin-thompson-groups-nv-are-a-t-menable`
  for every `n ≥ 2`.
- If false, the normal-pair refutation route is closed, and any refutation of the Haagerup
  property of `[[X]]` needs a non-normal relative-(T) subset.

## Forced shape

By `wobbling-normal-relative-t-subgroups-are-locally-finite`:
- `H` is locally finite. It contains no element of infinite order, and no infinite finitely
  generated subgroup.
- A finitely generated `H' ≤ H` whose generators have jumps at most `c` has all its orbits on each
  aperiodic `σ`-orbit bounded by `2 max(L_0, 2c)`.
- On every aperiodic orbit, every window of length `L ≥ L_0` has at most a `2δ²` fraction of
  points whose `H`-orbit is larger than `2L`.

By `subexponential-schreier-growth-excludes-sl3z-and-bs1k`, no infinite-order element of a finitely
generated subgroup of `Γ` is exponentially distorted.

## Candidate

The natural candidate is `Γ_p = EL_2(F_p[t, t^{-1}]) ⋉ F_p[t, t^{-1}]²` with `H` the base. The pair
has relative (T) by `elementary-linear-semidir-pair-relative-t`, and the base is an infinite
elementary abelian `p`-group, so the forced shape above does not exclude it.
- Whether `Γ_p` is residually finite and whether its infinite-order elements are undistorted have
  not been checked here. Both are necessary conditions, by
  `full-shift-topological-full-group-is-residually-finite` and the distortion bound.
- A first falsifiable test: does `Γ_p` act faithfully on `Z` by bounded-displacement bijections at
  all, that is, does `Γ_p` embed in `W(Z)`?

## Attempts

- **2026-09-19 (swarm-0917-w17-w17-nv-last1): Salo lamplighter realizations of the base (no
  witness yet; deferred).**
  - Salo (arXiv:2103.06663) embeds `A ≀_Ω G` in `[[X]]` when `G ≤ [[X]]` acts on `Ω` with suitable
    moves. The resulting base modules are quotients of `A[G]` that embed in products of
    permutation modules `A[G/G_x]` over points `x`.
  - For the plain orbit module, the point-indicator characters form a `G`-set of linear growth,
    since `W(Z)`-orbits have linear growth. That `G`-set is amenable, so the permutation
    representation on it has almost invariant vectors and no base-invariant vector. So the plain
    orbit module never has relative (T). This was checked in outline, not written as a node.
  - To realize `F_p[t,t^{-1}]²` with relative (T), the characters of the base must avoid every such
    amenable orbit family. By `elementary-linear-semidir-pair-relative-t`, the character space of
    `F_p[t,t^{-1}]²` carries no `EL_2`-almost-invariant probabilities near `0`.
  - So a realization needs a submodule whose dual sees no point-indicator characters. It is not
    known whether Salo's construction can produce one.
  - **Next falsifiable step:** decide whether `Γ_p` embeds in `W(Z)` at all. For example, test
    whether its Schreier graphs on some faithful action can have bounded bandwidth.
- **2026-09-19 (swarm-0917-w19-w19-nv-pull): the candidate `Γ_p` is refuted; it does not embed in
  `W(Z)`.** See `laurent-elementary-semidirect-product-is-not-in-wobbling-group`, established by
  `laurent-elementary-semidirect-not-in-wobbling-proof`. Every `ρ: Γ_p → W(Z)` kills an infinite
  subgroup of the base. Where each part of the argument does its work:
  - **Relative (T) makes base orbits finite.** Relative (T) plus normality gives a uniform
    `(Q, κ)`. Testing it on `1_J` for intervals `J` shows that every `H`-orbit is finite.
  - **(τ) bounds the finite `Γ`-orbits.** On a finite orbit, the half-indicator vector is
    `O(1/n)`-invariant. Relative (T) pushes it into `ℓ²(O)^H ≅ ℓ²(O/H)`. There, (τ) of `SL_2(R)`
    for all finite-index subgroups caps `n`. That (τ) comes from Serre's finite congruence kernel
    (`|S| = 2`) plus the Drinfeld Selberg property.
  - **Congruence on the infinite orbits.** There are at most `2r` infinite orbits. On each one,
    the `u_s` for `s ∈ span{t^{2k} : |k| ≤ N}` would produce `p^{2N+1}` characters inside a
    Schreier ball of linear size. So a nonzero ideal `I` has `I R²` acting trivially there.
  - Cornulier's FW theorem does not apply, since `E` fails FA.
- **Class kill.** Take any `(Γ, H)` with relative (T), `H ⊴ Γ`, and `Γ/H` with (τ) for all
  finite-index subgroups. In any bounded-displacement action, `Γ` acts through a finite quotient
  on `Z_fin`, and `H` is seen faithfully only on at most `2r` infinite orbits, with finite
  `H`-orbits there. So:
  - arithmetic quotients over module bases `R^n` with a contracting diagonal element are dead;
  - a surviving witness needs `Γ/H` without (τ) on its finite-index subgroups, or a base whose
    character orbits on one infinite `Γ`-orbit grow at most linearly under the `Γ/H`-action.
  - Linear growth of character orbits under `Γ/H` is an amenability-type condition. It pulls
    against relative (T), in the way the w17 lamplighter observation above does.
- **Next falsifiable step:** decide whether a relative-(T) pair with a locally finite base can have
  `Γ/H`-orbits on `Ĥ` of linear growth near the trivial character, or show that relative (T)
  forces exponential growth there. The second would close this claim negatively for all `Γ/H`
  with (τ).
