---
rg: 2
id: hs-normalization-profile-rounding-crux
kind: claim
title: Property (T) rounds approximate commutant centers to exact ones with a controlled irreducible-dimension profile
distinct_from:
  kt-centralizer-normalization-hs: that is the full normalization statement in every tracial matrix ultraproduct; this is the single finite-stage rounding lemma that, together with median concentration, would prove it, isolated so it can be attacked or refuted on its own.
  hs-per-atom-compressor-clause-is-vacuous: that shows the per-atom transport clause carries no size information on atoms of trace below eps^2/4; this asks for the mass-weighted rounding that survives exactly that regime, and states it as the open finite-stage lemma.
  fd-isotypic-part-of-a-kazhdan-image-carries-no-wall: that normalizes the finite-dimensional isotypic part of a genuine image with no approximation; this is the approximate-representation rounding statement, whose whole difficulty is that the approximate commutant center is not a genuine isotypic decomposition.
  invariant-size-collapse: that is the exact algebraic collapse under a faithful conjugation-invariant strictly monotone size; this is the quantitative finite-stage substitute that must supply such a size where the trace cannot, because the trace is refinement-blind.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**OPEN. The single crux of the positive branch.** Let `Gamma` be a group with
Kazhdan's property (T), finite generating set `F`, and Kazhdan gap `kappa`.
Let `sigma_n : Gamma -> U(n)` be maps with multiplicative defect
`max_(s,s' in F) ||sigma_n(ss') - sigma_n(s)sigma_n(s')||_2 <= eps` (normalized
Hilbert--Schmidt norm). Write `A_n(delta)` for the `delta`-approximate
commutant `{x in M_n : max_(s in F) ||[x, sigma_n(s)]||_2 <= delta}`.

**Claim.** There is a function `f(eps, delta, kappa) -> 0` as `eps, delta -> 0`,
uniform in `n`, such that every projection `p` with

```text
p in A_n(delta),      max_(s in F) ||[p, sigma_n(s)]||_2 <= delta,
```

that is `delta`-central in `A_n(delta)` is within `f` in 2-norm of a
projection `q` in the center of the exact commutant `sigma_n(Gamma)' cap M_n`
whose normalized irreducible-dimension profile (the trace-weighted
distribution of `q` over the minimal central projections of
`sigma_n(Gamma)'' cap M_n`) is within `f` of that of `p`.

This is the Hilbert--Schmidt analogue of the finite-stage object Kun--Thom's
proof of Theorem 4.1 runs its two median arguments on: the vertex masses and
isotropy orders of the cluster groupoid of expander components. Their object
is a genuine partition of a point set; this asks for the same object as an
exactly-central projection with a controlled dimension profile, extracted from
an approximate unitary representation.

**Why it is the crux.** With this lemma in hand, the positive branch of
`hyperlinear-groups-kill-rigid-compression-defects` closes:
`median-poincare-concentration` and `tracial-median-concentration` turn the
rounded profile, made almost `G`-invariant by property (T) of `G`, into an
asymptotically compressor-conserved size; monotonicity of the commutant along a
compressor (`Ad sigma(t)` grows `A` one-sidedly) plus a conserved strictly
monotone size forces `Ad sigma(t)` to preserve the center, which is
normalization. The reduction skeleton is artifact Section 11; only this lemma
and the concentration step remain open, so it is posed here as a standalone
target rather than asserted as a proof route.

## Attempts

- **Projection rounding alone (available).** Property (T) rounds a single
  `delta`-almost-invariant projection to an exactly `sigma_n(Gamma)`-invariant
  one within `O(delta/kappa)` in 2-norm. This is axioms (A1), (A2), (A4) of the
  conservation criterion (artifact Section 10) and is not the obstacle.
- **The profile is the obstacle, on small blocks.** The rounding above is
  vacuous exactly where the profile lives. A minimal central projection of
  trace below `delta^2/(4 kappa^2)` is `delta`-almost-invariant for the trivial
  reason that its 2-norm is already that small
  (`hs-per-atom-compressor-clause-is-vacuous`), so property (T) returns no
  information about it. In a regular-type model the irreducible blocks have
  vanishing trace, so order-one mass sits in exactly this unprotected regime.
  The mass-weighted clause `sum_j ||W p_j W^* - p_(sigma(j))||_2^2 <= eps` is
  what survives it, and property (T) alone is not known to supply that clause:
  `nonmonomial-multiplicity-obstructs-hs-compressor-transport` builds an exact
  representation of a Kazhdan pair for which no such coordinate matching exists,
  so the input is a monomiality/coordinate-algebra fact, not a consequence of
  rigidity.
- **The only conjugation-invariant tracial size is refinement-blind.** By
  `invariant-size-collapse` the trace cannot be the strictly monotone size the
  median step consumes; the finite-stage dimension profile is the sole
  remaining candidate, which is why the lemma is posed at finite `n` rather than
  in the von Neumann limit.
- **Uniform-(T) is unavailable for the linear instance.** Lubotzky--Yao
  (arXiv:2608.03561v2) show every infinite finitely generated linear group,
  `SL_n(Z)` included, fails uniform property (T). The Kun--Thom Theorem E pair
  is linear, so any use of `kappa` must be at a fixed generating set; a rounding
  bound that degrades as the generating set varies cannot be invoked. This is
  recorded as `uniform-kazhdan-fails-for-linear-theorem-e-pair`.
