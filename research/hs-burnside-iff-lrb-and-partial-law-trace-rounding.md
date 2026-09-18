---
rg: 2
id: hs-burnside-iff-lrb-and-partial-law-trace-rounding
kind: claim
title: Hyperlinear groups of exponent N are finite iff the local restricted Burnside principle holds and approximate exponent-N traces round to exact partial Burnside representations
distinct_from:
  hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness: that identifies the finiteness statement with trace rigidity of approximate models, a single statement; this splits it into a finite-group principle and an exact trace-rounding principle, each necessary, which together are sufficient.
  local-restricted-burnside-iff-lef-burnside-groups-are-finite: that identifies the local restricted Burnside principle with finiteness of LEF groups of exponent N; this shows that principle is necessary for the hyperlinear statement and names the analytic complement that upgrades it to sufficiency.
  bounded-degree-partial-burnside-reps-factor-through-burnside: that concerns exact representations of bounded degree satisfying the law on short words; this concerns traces of approximate models in unbounded degree, rounded to exact partial-law representations.
  matrix-restricted-burnside-gap: that is the operator-norm, dimension-free power-law inequality; this is a normalized Hilbert--Schmidt statement at the level of limit traces.
  hyperlinear-fg-bounded-exponent-groups-are-finite: that is the open finiteness statement; this is the established decomposition of it into two prerequisites.
---

**ESTABLISHED.** Fix `m, N >= 2`. Approximate exponent-N models and their limit
traces `tau` are as in
`hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness`. The partial
Burnside groups `Π_R(m,N)`, `LRB(R, C)` and `LRB(m,N)` are as in
`local-restricted-burnside-iff-partial-burnside-finite-quotients`. Write
`HB(m,N)` for "every `m`-generated hyperlinear group of exponent dividing `N`
is finite".

**Definition.** `S(m,N,R)` (exact partial-law trace rounding at radius `R`)
means: for every approximate exponent-N model with limit trace `tau`, there are
finite-dimensional unitary representations `rho_j` of `Π_R(m,N)` such that
`tr rho_j(w) -> tau(w)` for every `w in F_m`. Here `rho_j(w)` is evaluated
through `F_m -> Π_R(m,N)` and `tr` is normalized. Since `Π_{R'}(m,N)` is a
quotient of `Π_R(m,N)` for `R' >= R`, `S(m,N,R')` implies `S(m,N,R)`: the
rounding gets harder as the radius grows, while `LRB(R, C)` gets easier.

**Statement.**
1. **(a) The finite-group prerequisite is necessary.** `HB(m,N)` implies
   `LRB(m,N)`.
2. **(b) The analytic prerequisite is necessary.** `HB(m,N)` implies
   `S(m,N,R)` for every `R >= 1`. In fact the `rho_j` can be chosen to factor
   through a finite quotient of `B(m,N)`.
3. **(c) Sufficiency.** If `LRB(R_0, C)` holds and `S(m,N,R)` holds for some
   `R >= R_0`, then `HB(m,N)` holds. Moreover every limit trace `tau` then
   factors through the restricted Burnside group `R(m,N)`.
4. **Decomposition.**

   ```text
   HB(m,N)  <=>  LRB(m,N) and S(m,N,R) for all R
            <=>  there are R, C with LRB(R, C) and S(m,N,R).
   ```

5. **(d) Stability cannot supply the analytic prerequisite at an LRB radius.**
   Suppose `LRB(R_0, C)` holds, `R >= R_0`, and `B(m,N)` is infinite. If
   `Π_R(m,N)` is flexibly Hilbert--Schmidt stable (in the sense of
   `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, which includes
   strict stability), then `Π_R(m,N)` is not hyperlinear. `Π_R(m,N)` is
   finitely presented. So any proof of `S(m,N,R)` by stability of the partial
   Burnside group at a radius where the local principle holds produces a
   finitely presented non-hyperlinear group on the way. That is at least as
   strong as the root `non-hyperlinear-group`.

## Consequences

- **The flagship Burnside route splits into two prerequisites that can fail
  separately.** For a large odd exponent, the finiteness input of
  `non-hyperlinear-group-via-hyperlinear-burnside-finiteness` is equivalent to
  the conjunction of
  - `large-odd-exponent-local-restricted-burnside`, a statement about finite
    groups only. It implies a non-residually-finite hyperbolic group, and
  - `approximate-exponent-traces-round-to-partial-burnside-reps`, an exact
    rounding statement for unitary matrices with no finiteness hypothesis.

  Clause 3 of `local-restricted-burnside-iff-lef-burnside-groups-are-finite`
  gives LEF witnesses to a failure of `LRB`. Their traces are limits of regular
  representations of finite groups that satisfy the law exactly on growing
  balls, so they satisfy `S(m,N,R)` for every `R`. So a failure of the
  finite-group prerequisite does not by itself refute the analytic one.
  Conversely, nothing known makes `S` follow from `LRB`.
- **What a counterexample must look like.** If `LRB(m,N)` holds, a counterexample
  to `HB(m,N)` is an approximate exponent-N model whose limit trace is not a limit
  of traces of genuine linear representations that satisfy the exponent law
  exactly on a ball of radius `R_0`. Trace-level approximation by exact
  partial-law models already forces finiteness.
- **The radius the rounding must reach.** By
  `partial-burnside-presentations-are-golod-shafarevich`, an `LRB` radius
  exceeds `(q - 5)/4` for every prime power `q` dividing `N`. So the rounding in
  clause 3 must be exact on words of at least that length. At radius `1` it is
  elementary (see `approximate-exponent-traces-round-to-partial-burnside-reps`).
- **Bounded degree needs no LRB.** If the `rho_j` in `S(m,N,R)` have bounded
  degree `d` and `R >= R_0(m,N,d)` of
  `bounded-degree-partial-burnside-reps-factor-through-burnside`, clause 2 there
  bounds their orders by `f(d) N^d`. Step (c)3 of the proof then gives
  `HB(m,N)` without `LRB`. `LRB` is exactly what controls unbounded degree.

No novelty is claimed. The ingredients are standard. What is new here is the
decomposition and the calibration in (d).

DERIVATION
hs-burnside-iff-lrb-and-partial-law-trace-rounding-proof
