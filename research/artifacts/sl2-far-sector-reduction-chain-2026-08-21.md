# SL2 far-sector reduction chain

**Archived 2026-08-21.** This is a program map indexing proved and open links,
not a standalone Cairn claim.

The `SL_2(Z[1/2])` far sector is now a single chain, each link proved,
cited, or reduced to the next:

1. `far-sector-vertex-handled-edge-is-square-root` -- vertex handled by
   Gerasimova--Shchepin; only the half-parabolic edge is open.
2. Both parabolic skeletons are `BS(1,4)` and HS-stable
   (Levit--Vigdorovich), so exactify to finite ODD order.
3. `bs14-exact-representation-variety-is-hs-locally-rigid` (PROVED) --
   close exact skeletons are near-conjugate; share one exact `h`.
4. Define the lower tower by the swap: the `w(1)` relation is exact,
   all amplified defect removed, residual = two swap holonomies.
5. Steinberg cocycle syzygy `w(s)w(t)^{-1}=h(s/t)` -- collapses the two
   holonomies to one twisted-coboundary equation `c psi(c)^{-1}=e'`.
6. `psi = Ad(h)` is the pure `x4` shift (computed); `(psi_*-1)` is
   `x3` on the odd base, so the obstruction is `3`-primary
   (`= SL_2(Z)` torsion, via `4-1`).
7. `x4` fixes only order-`3` roots `{1,omega,omega^2}` (sparse); the
   regular trace makes their mass vanish, killing that obstruction.
8. The residual shrinking-gap locus is the near-identity band; there
   the `x4` gap and (by trace `->` Lebesgue) the spectral mass BOTH
   thin linearly, so the absorption cost is `~ delta log(1/delta)` --
   PROVIDED the defect near identity scales as mass, not `sqrt(mass)`.

The one open link is (8)'s exponent: the near-identity
commutator-mixing bound `||e'|_(rho-band)||_2 <~ rho`, expected from
unipotent normal generation of `SL_2(Z[1/2])` but requiring transfer
across the non-conjugation-invariant `V`-eigenband.  Establishing it
runs the chain into `iwahori-outlier-repair` and to the goal.

## Attempts

- The chain is assembled and each cited link verified in its own node;
  the residual is isolated in `solenoid-absorption-cascade-converges`.
  The next action is the band-mixing bound alone.
