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
- **2026-09-20 (swarm-0917-w23-w23-nv-break): a free linear part is enough for relative (T) (new
  witness class; no embedding yet).**
  - `char-p-burger-pairs-for-nonamenable-subgroups-of-sl2-fq-t` (ESTABLISHED in this lane, not
    reviewed) proves that `(Λ ⋉ F_q[t]², F_q[t]²)` has relative (T) for *every* non-amenable
    `Λ ≤ SL_2(F_q[t])`, and in particular for a free `F ≤ SL_2(F_q[t])`. The route is Burger's: an
    invariant mean on `P¹(F_q((1/t)))`, then the amenable boundary action of the Bruhat–Tits tree.
  - So a copy of `F ⋉ F_q[t]²` in `[[X]]` suffices. It is a subgroup of `Γ_p`, so it is a strictly
    weaker target than `Γ_p`. Its base is locally finite, as the forced shape requires.
  - Its quotient `F` fails (τ) and fails property FM. So the wave 18–21 class kills that need a (τ)
    or FM quotient do not reach it (live-bus nodes, not in this worktree).
  - The rank-two affine kill of wave 19 still applies when `F ⋉ F_q[t]²` is finitely generated. It
    then asks for a uniform spectral gap of `F` on congruence-type finite quotients, which is a
    super-strong-approximation question for thin subgroups of `SL_2(F_q[t])`. The countable version,
    with `F_q[t]²` not finitely generated as an `F`-module, is outside that kill.
  - Not established: relative (T) for a finitely generated `F`-submodule `N ⊂ F_q[t]²` of infinite
    index. The proof above uses that `M` is all of `R²`, through duality with `K²/R²`.
  - **Next falsifiable step:** embed the countable group `F ⋉ F_q[t]²` in `W(Z)`, or in `[[X]]`, by a
    one-sided linear-CA lamp realization over `(F_p²)^N`, in the manner of the lifting criterion of
    `char-p-burger-lamp-realizations-refute-haagerup`, with the linear part only free.
    Alternatively, show that every faithful bounded-displacement action of it has amenable
    character orbits near `0`.
