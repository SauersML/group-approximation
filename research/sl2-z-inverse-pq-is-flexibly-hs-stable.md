---
rg: 2
id: sl2-z-inverse-pq-is-flexibly-hs-stable
kind: claim
title: SL2(Z[1/pq]) is flexibly Hilbert--Schmidt stable
distinct_from:
  sl2-z-inverse-pq-is-hs-stable: that is the same-dimension notion, which is refuted by sl2-z-inverse-pq-is-not-strictly-hs-stable; this allows the exact representation to live in dimension D_n with D_n/d_n -> 1, which repairs the Steinberg compressions that kill the strict notion.
  iwahori-local-global-defect-question: that is flexible stability of SL_2(Z[1/2]), a lattice in SL_2(R) x SL_2(Q_2) with one finite place; this is the lattice with two finite places, whose tree action for q comes with a co-dense (T;FD) subgroup SL_2(Z[1/p]) and so feeds the HNN theorem directly.
  sln-z-flexibly-hs-stable: that is flexible stability of the higher-rank lattice SL_n(Z); this is the rank-one-factor S-arithmetic lattice SL_2(Z[1/pq]).
---

**OPEN.**  For primes `p != q`, `SL_2(Z[1/pq])` is flexibly HS-stable in the
sense of Dogon--Vigdorovich, Definition 1.2 of arXiv:2506.20843.  For every
sequence of unitary tuples `phi_n` of dimension `d_n` on a fixed finite
generating set, with relator defect `-> 0`, there are exact unitary
representations `rho_n` of dimension `D_n >= d_n` with `D_n/d_n -> 1` whose
compressions `P_n rho_n(s) P_n` to a `d_n`-dimensional subspace are within
`o(1)` of `phi_n(s)` in normalized Hilbert--Schmidt norm on generators.
This is the form recorded in `amenable-flexible-hs-stability-is-strict-hs-stability`;
strict stability is the case `D_n = d_n`.

**What is known.**
- The strict version is false (`sl2-z-inverse-pq-is-not-strictly-hs-stable`).
- The one-dimensional polar compressions of irreducible representations
  that refute the strict version are flexibly repaired by one dimension
  (`tfd-unbounded-irreps-group-is-not-strictly-hs-stable`, last paragraph of
  its proof), and more generally low-leakage compressions over (T;FD) round
  flexibly (`tfd-low-leakage-compressions-flexibly-reduce`).
- `SL_2(Z[1/pq])` is residually finite with (T;FD), and every
  finite-dimensional unitary representation factors through a congruence
  quotient (`sl2-s-arithmetic-pair-is-codense-kazhdan`, item 3).  So any
  flexible repair lands on congruence representations.

**Why it matters.**  With `sl2-s-arithmetic-pair-is-codense-kazhdan` and
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` (Corollary, explicit
instance (HC3)), this claim makes
`<SL_2(Z[1/pq]), t | [t, SL_2(Z[1/p])] = 1>` nonhyperlinear.  By the strict
refutation it would also settle `flexibly-but-not-strictly-hs-stable-group-exists`.

**What would refute it.**  A sequence of asymptotic representations whose
limit trace is not a limit of traces of congruence representations, or
which is not almost a sum of almost-representations coming from exact
congruence representations up to a vanishing proportion of dimensions.

## Attempts

**2026-09-17, swarm-0917-w6-w6-nh-last2 (creation only).**  Split off from
`sl2-z-inverse-pq-is-hs-stable` after the strict version was refuted by
Steinberg compressions.  No attack on the flexible version has been made
here.

**2026-09-18, swarm-0917-w13-w13-nh-follow (new decomposition, refutation
route closed).** The status stays OPEN. The node now reduces to the
one-prime node `sl2-z-inverse-p-is-flexibly-hs-stable`, through the route
`sl2-pq-flexibility-from-sl2-p-flexibility`.

- **Local theorem, for every prime `q`:** `iwahori-depth-drift-bounds-smooth-vertex-mismatch`.
  - Smooth representations of `SL_2(Z_q)` and of its `diag(q,1)`-conjugate
    have Iwahori mismatch `ε >= (1-θ)(q-1)/(q+1)`, where `θ` is the
    vertex-trivial fraction.
  - The bound is sharp.
  - The certificate is the depth drift `d_1 - d_0` of Iwahori irreducibles.
- **Global repair:** `sl2-pq-exact-vertex-pairs-have-uniform-linear-repair`.
  - It uses the congruence property of `SL_2(Z[1/p])` and (T;FD) of the edge group `D`.
  - Every pair of exact representations of the two vertex groups of
    `A = C *_D C'` with edge defect `δ` is within `Kδ` of one exact
    representation of `A`.
- **What is killed.** Gluing exact or congruence vertex representations
  along the q-adic tree cannot produce a counterexample.
- **What is left.** Only the vertex group's own stability, which is
  Dogon--Vigdorovich Question 1.4 when `p = 2`.
