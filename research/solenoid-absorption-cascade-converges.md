---
rg: 2
id: solenoid-absorption-cascade-converges
kind: claim
title: The twisted-coboundary absorption cascade on an odd solenoid tower converges dimension-free
distinct_from:
  skeleton-relative-hs-stability-for-sl2: that is the SL2 gluing claim that consumes this as its sole analytic lemma; this is the self-contained convergence inequality on a solenoid tower, with no SL2 and no swap.
  bs14-exact-representation-variety-is-hs-locally-rigid: that near-conjugates two close EXACT representations; this solves a single twisted-coboundary equation for the CORRECTION unitary and bounds it, the step the gluing needs after rigidity has aligned the pieces.
---

Let `(V, W)` be an exact finite-dimensional `BS(1,4)` representation
(base `V` of finite odd order, `W V W^{-1} = V^4`), let `Z` be its
commutant, and let `psi : Z -> Z` be the unital trace-preserving
`*`-automorphism given by the solenoid shift composed with a fixed
swap transport (the map appearing in the skeleton `(R1)` equation).
Given `e in U(Z)` with `||e - 1||_2 <= delta`, seek `c in U(Z)` with

```text
psi(c) c^{-1} = e     (up to a residual pushed to the next level).
```

CLAIM: there is a dimension-free modulus `g(delta) -> 0` and a
solution with `||c - 1||_2 <= g(delta)`, obtained by the peeling
cascade below; equivalently the twisted coboundary equation is
solvable to `o(1)` with dimension-free loss, uniformly over the exact
odd tower.

## Mechanism (peel off-diagonal, pass diagonal down)

`Z` splits along `V`-eigenspaces; on each `psi`-orbit of commutant
blocks with return monodromy `M`, the twisted-commutator map
`c |-> M c M^{-1} c^{-1}` has differential `Ad(M) - 1`, an isomorphism
EXACTLY on the off-`M`-centralizer directions with lower bound the
eigenvalue gap `gamma(M)`.  So:

1. **Off-diagonal peel (spread part).**  The component of the orbit
   holonomy `H(e)` orthogonal to `M`'s centralizer is absorbed by a
   correction with `||c_1||_2 <= ||H_off||_2 / gamma(M)`; this is an
   exact quantitative submersion, no smallness of `M` needed.
2. **Diagonal descent (resonant part).**  The residual is the
   `M`-centralizer (diagonal-in-eigenbasis) component of `H` -- a
   tuple of phases on the eigenspaces.  It cannot be conjugated away,
   but the eigenspace multiplicities carry the NEXT finer level of the
   same odd solenoid tower (the fourth-root refinement), on which the
   residual is again a twisted coboundary with its own monodromy;
   recurse.

The tower has finite depth `n` per fixed relator accuracy, so the
recursion terminates; the total correction is
`||c||_2 <= sum_(k<n) ||H_off^(k)||_2 / gamma_k`.

## Attempts

- **The convergence is now ONE concrete inequality.**  On the odd
  model the level-`k` gaps `gamma_k` are spacings of odd roots of
  unity at the `k`-th fourth-root refinement, and the peeled
  residuals `||H_off^(k)||_2` are residuals-of-residuals, each bounded
  by the previous level's uncorrected part times the local defect.
  Dimension-free convergence is exactly
  `sum_k ||H_off^(k)||_2 / gamma_k -> 0` as `delta -> 0`, uniformly in
  dimension.  This is a statement about a fixed compact dynamical
  system (the `x4` odometer on the dyadic solenoid) with NO group
  theory left -- the cleanest possible form of the residual analytic
  content.
- **Snag + fix (2026-08-21).** Naive peel does not converge: the diagonal residual descends at fixed size delta while 1/gamma_k grows. Fix: alternate off-diagonal conjugation with absorbing the diagonal into the exact base-torus reparametrization (free); only the reduced cycle-cocycle (dim = tower cycles - 1) descends, and lemma (b) is its contraction under alternating absorption.
- **Reduction to (psi_*-1) invertibility; obstruction is 3-PRIMARY (2026-08-21).** The residual is a class in finite-dim H^1(tower cycle-graph); the equation projects to (psi_*-1)[c]=[e], so lemma (b) = invertibility of psi_*-1. psi carries x4 and 4-1=3, so the cokernel is 3-primary only - the two-adic far sector's final obstruction sits at the prime 3. Finite question: does the SL2(Z[1/2]) relation-defect class carry 3-primary cohomology?
- **3-primary obstruction governed by K_2(Z[1/2]), 3-torsion-free (2026-08-21).** Defect class lives in the relation module ~ K_2(Z[1/2]); localization K_2(Z)=Z/2 -> K_2(Z[1/2]) -> K_1(F_2)=0 gives it in {0, Z/2}, 3-torsion-free, so [e]'s 3-primary part vanishes and (psi_*-1) inverts, closing lemma (b) - modulo the link that the analytic defect factors through the algebraic relation module.
- **Elementary spectral form of the same prime-3 fact (2026-08-21).**
  Concretely, `(psi_* - 1)` acts on the discrete cycle data as
  multiplication by `4 - 1 = 3` on `Z/N` (`N` = odd order of the exact
  base, the spectrum being a union of `x4`-orbits of `N`-th roots of
  unity).  Mult-by-3 on `Z/N` is an isomorphism unless `3 | N`, and
  its kernel/cokernel is exactly the `3`-primary subgroup of `Z/N`.
  So `(psi_* - 1)` is invertible -- and lemma (b) closes with no
  condition on `[e]` at all -- WHENEVER the Levit--Vigdorovich
  exact base can be taken of order coprime to `3`, or more weakly
  whenever the microstate defect places no spectral mass on the
  `3`-primary `x4`-orbits.  This is the same prime-3 conclusion as the
  `K_2(Z[1/2])` framing, in fully elementary terms, and it isolates
  the exact deciding question: is there any obstruction to choosing
  the exact odd base `3`-coprime (equivalently, can the unipotent's
  approximate spectrum concentrate on cube-power roots of unity)?  The
  `x4`-invariance is the only constraint on the spectrum and it does
  NOT force `3 | N`, so the expected answer is that a `3`-coprime
  exactification always exists and lemma (b) closes unconditionally --
  the last thing to verify is that the LV modulus survives restricting
  the target spectrum to `3`-coprime supports.
- **Caveat: the exact arithmetic depends on the precise `psi_*`
  (2026-08-21, must verify before trusting `prime 3`).**  The clean
  `4 - 1 = 3` uses `psi_*` = the PURE shift `x4`.  The actual `psi`
  is the shift composed with the swap transport, and depending on how
  the swap acts on `H^1` the relevant operator could be `x4 - 1` (3),
  or `x16 - 1 = x(4^2) - 1` (15 = 3.5) if the swap squares the shift,
  or -- the dangerous case -- an involution-like map with a large
  fixed space that would make `(psi_* - 1)` FAR from invertible.  A
  naive model where `psi` swaps two `x4`/`x(1/4)` copies gives
  `psi^2 = 1` with a big `+1`-eigenspace, which would BREAK the clean
  story; the resolution is that `psi` acts on the single upper
  commutant (the swap transport returns lower data to the upper
  frame), not as a genuine two-copy swap, so the pure-shift model is
  the likely correct one -- but this MUST be computed explicitly
  before the `prime 3` conclusion is relied on.  Recording it as the
  first thing to check: write `psi_*` on `H^1(Z_upper)` from the
  Steinberg swap-and-torus words and read off its `1`-eigenspace.
  Everything downstream (K_2 3-torsion-freeness, 3-coprime base)
  is correct arithmetic ONLY once `psi_*` is confirmed to reduce to a
  fixed-point-free-plus-`x4` form.
- **Why it is plausible and where it could fail.**  The peeling is a
  geometric contraction when the residual shrinks faster than the gap:
  each descent multiplies the uncorrected mass by the local defect
  `O(delta)` while dividing by `gamma_k`.  If `gamma_k` shrinks only
  polynomially in the level while the residual shrinks geometrically,
  the sum converges (expected case).  It could fail only if the odd
  orders grow so fast that `1/gamma_k` outruns the geometric residual
  decay -- a resonance between tower depth and odd-order growth,
  checkable directly on the odometer without any `SL_2` input.  That
  resonance check is the single remaining question, and it is finite
  per level and self-similar across levels (a transfer-operator
  spectral radius on the odometer).
