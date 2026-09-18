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

**2026-09-18, swarm-0917-w12-w12-nh-break (family reframing, belief breaker).**
Result: the first refutation clause above is vacuous. The node reduces to the
center-supported microstate face, and it is gated by `F_2^3`. Status stays OPEN.

- **Every character of `A = SL_2(Z[1/pq])` is a limit of congruence traces.**
  So no refutation can work at trace level.
  - `Z[1/pq]^x = {±p^a q^b}` is infinite. So Peterson--Thom character rigidity
    (arXiv:1303.4007, `SL_2` over rings of `S`-integers with infinitely many
    units) applies. Every extremal character either factors through a finite
    quotient or is supported on the center `{±1}`.
  - `S = {∞, p, q}` has at least two places. By Serre's congruence subgroup theorem
    for `SL_2`, every finite-index subgroup is congruence. So the finite-quotient
    extremes are normalized traces of congruence representations.
  - There are two center-supported extremes: `delta_e`, and `chi_-` with
    `chi_-(-1) = -1` and zero off the center.
    - Let `N` run over integers `>= 3` prime to `pq`, ordered by divisibility.
    - `delta_e` is the pointwise limit of `1_(Gamma(N))`, the normalized traces
      of the regular representations of `SL_2(Z/N)`. This uses
      `intersection Gamma(N) = {e}` and `-1 ∉ Gamma(N)`.
    - `chi_-` is the limit of the normalized traces of the representations
      induced from the character of `±Gamma(N)` that is `-1` at `-1`.
  - Characters form a Choquet simplex, and pointwise convergence is tested one
    group element at a time. So an arbitrary character is a pointwise limit of
    finite rational convex combinations of extremes. Those combinations are
    limits of normalized traces of direct sums of congruence representations.
  - The first clause of "What would refute it" therefore never occurs. This is
    the pq analogue of what `bs14-character-split-leaves-only-the-regular-microstate-face`
    records for `p = 2`. The proof above does not use Dogon--Vigdorovich
    Theorem 1.6.
- **What survives is the center-supported microstate face.**
  - Run the central cut of `bs14-character-split-leaves-only-the-regular-microstate-face`
    for this `A`: the projection `z_fin` onto the finite-character part, lifted to
    asymptotically commuting matrix projections.
  - It splits any asymptotic representation into two pieces, with vanishing
    normalized-HS error:
    - a hyperfinite corner, which the hyperfinite HS stability argument used there
      corrects to exact congruence representations;
    - a corner whose trace is `(1 - z)delta_e + z chi_-`, with `z` fixed by the
      spectral projection of `pi(-1)`.
  - `pi(-1)` is central and asymptotically an involution. Splitting by its two
    eigenspaces leaves two pure faces, `delta_e` and `chi_-`. The GNS algebras are
    `L(A)` and its twisted form, and neither is amenable.
  - So the whole node is equivalent to its restriction to microstates of the
    regular (and sign-twisted regular) character. The second refutation clause,
    "not almost a sum of almost-representations from exact congruence
    representations", can only be witnessed there.
  - The low-leakage rounding (`tfd-low-leakage-compressions-flexibly-reduce`)
    and the one-dimensional Steinberg repairs are statements about the finite
    corner. They say nothing about this face.
- **It is gated at `F_2^3`, invariant ME class.** By (K3) of
  `sl2-pair-witnesses-need-non-ce-f2xf2-action`, a proof of this node yields an
  essentially free p.m.p. action of `F_2^3` with a non-CE crossed product.
  - `A` is measure equivalent to `F_2^3`, being a lattice in
    `SL_2(R) x SL_2(Q_p) x SL_2(Q_q)`.
  - So a proof must see something beyond the ME class. Congruence level, `(T;FD)`
    and tree co-density are all invisible to `F_2^3`.
  - Conversely, `f2xf2-crossed-products-are-connes-embeddable` in its `F_2^3`
    form would refute this node through the same chain.
- **Failing step for trace-level refutations.** Such a refutation has to produce a
  character outside the closed congruence hull. Peterson--Thom plus the
  congruence subgroup property makes that hull all of `Char(A)`.
