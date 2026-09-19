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
- **2026-09-19 (swarm-0917-w19-w19-nv-follow): R-core rank of point stabilisers (class kill for
  rank-two affine witnesses with (τ); the claim stays OPEN).**
  - `rank-two-affine-relative-t-pairs-in-wobbling-groups-fail-tau` is ESTABLISHED by a
    self-contained route. Its setting: `R` is any infinite commutative domain, `Λ ≤ GL_2(R)` is
    arbitrary, `Γ = Λ ⋉ R²` is finitely generated, and `(Γ, R²)` has relative (T).
  - For every bounded-displacement action of such a `Γ` on `Z`:
    - some `dR²` with `d ≠ 0` acts trivially on every orbit, finite or infinite;
    - faithfulness forces unbounded finite orbits `O` on which `Λ` has no uniform spectral gap on
      the `Λ`-sets `O/A`.
  - So no such pair with `Λ` having (τ) lives in `W(Z)` or `[[X]]`.
  - Key step: the stabiliser in `Λ` of a finite-index `V ≤ R²` is virtually metabelian unless the
    largest `R`-submodule inside `V` has rank two. Relative (T) makes that stabiliser co-amenable
    and makes `Λ` non-amenable.
  - This removes the need for a contracting diagonal element or an exponential-growth estimate on
    characters. Every earlier argument for the named candidate used one of these, as did the class
    kill recorded in wave 19 by w19-nv-pull, which is not yet on this branch.
  - The named candidate `Γ_p` falls under it once (τ) for `SL_2(F_p[t,t^-1])` is imported, and
    that import is not recorded here with a verbatim citation.
  - **Where a witness must now live.** Take `H` abelian with a rank-two module structure over a
    domain. Then `Γ/H` must fail (τ), precisely along the finite `Λ`-sets `O/A`, which lie over
    congruence quotients `Λ ⋉ (R/dR)²`. Otherwise `H` needs rank at least 3, or is not a
    torsion-free module over a domain.
  - For rank `n ≥ 3` the rank lemma leaves a stabiliser containing `GL(W)`, which is not amenable.
    The obstruction then needs co-amenability input on `Λ`.
  - **Next falsifiable step:** find a finitely generated `Λ ≤ SL_2(R)`, `R` an infinite domain of
    characteristic `p`, with `(Λ ⋉ R², R²)` relative (T), and with a family of finite quotients
    `Λ ⋉ (R/d_jR)²` whose Schreier graphs have bounded bandwidth. Or show that relative (T) of the
    pair forces (τ) on congruence quotients of `Λ`.
