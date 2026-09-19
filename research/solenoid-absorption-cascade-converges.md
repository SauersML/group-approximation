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
- **Caveat RESOLVED by computation: `psi_* = Ad(h)`, pure `x4`, no
  swap (2026-08-21).**  Compute the correction equation explicitly.
  The lower tower is defined by the swap, `L(y) = s e_+(-y) s^{-1}`,
  and `(R1)` is exactly the failure of the Weyl-torus relation
  `s h s^{-1} = h^{-1}` (a one-line check: `h L(y) h^{-1} = L(y/4)`
  holds iff `s h s^{-1} = h^{-1}`, using `h e_+(x) h^{-1} = e_+(4x)`).
  To fix it WITHOUT disturbing the exact upper tower, correct
  `s -> s c` with `c` in the base commutant `Z = {V}'`
  (`V = pi(u)`).  The resulting equation for `c` is
  `c (h c^{-1} h^{-1}) = e'`, i.e.

  ```text
  c psi(c)^{-1} = e',    psi = Ad(h) on Z = {V}'.
  ```

  `Ad(h)` maps the `V`-eigenspace of `lambda` to that of
  `lambda^(4^{±1})` (since `h V h^{-1} = V^4`), so `psi_*` is the PURE
  `x4` spectral shift on the discrete cycle data -- the swap `s` is
  NOT in the operator, it only enters the right-hand side `e'`.  The
  feared two-copy-swap model (`psi^2 = 1`, large fixed space) does not
  arise, because `c` lives in the single upper base commutant and the
  swap has been absorbed into the target.  Hence `(psi_* - 1)` is
  `4^{±1} - 1` on `Z/N` -- a unit times `3` either way -- and the
  `prime 3` conclusion is CONFIRMED, not conjectural: lemma (b)
  reduces to `(I)` a `3`-coprime `LV` exact base, or `(II)` `e'`
  avoiding the `3`-primary `x4`-orbits.  The K_2 and elementary
  framings above now both apply with the operator pinned down.
- **The true crux: cube-root eigenspaces, where `x4 = id` and the
  prime 3 is `SL_2(Z)` torsion (2026-08-21).**  `4 = 1 mod 3`, so on
  the `3`-primary spectrum the `x4` shift is the IDENTITY: there
  `(psi_* - 1) = 0`, the equation `c psi(c)^{-1} = e'` degenerates to
  `1 = e'`, and NO correction `c` can absorb a nontrivial `e'`.  So
  lemma (b) does not close unconditionally; it requires precisely that
  the Weyl-torus defect `e'` VANISH on the cube-root eigenspaces of
  `V = pi(u)`.  This is not an artifact: the cube and sixth roots of
  unity are exactly the eigenvalues of the order-3 and order-6
  ELLIPTIC elements of `SL_2(Z)` (whose abelianization is
  `Z/12 = Z/4 x Z/3`), so the prime `3` here IS `SL_2(Z)`'s torsion
  prime, arriving through `4 - 1`.  The remaining content is therefore
  a genuine arithmetic question, now sharply posed: in an accurate
  microstate, is the Weyl relation `s h s^{-1} = h^{-1}` defect forced
  to vanish on the subspace where `pi(u)` has order dividing `3`?  Two
  honest possibilities: (a) it vanishes -- because on that subspace
  the elliptic structure of `SL_2(Z)` is itself HS-stable (finite
  subgroups are stable, Gowers--Hatami), pinning the Weyl relation
  exactly there -- in which case lemma (b) closes and the far sector
  with it; (b) it does not, and the `3`-primary elliptic sector is a
  real residual obstruction, in which case the coset-Bernoulli /
  `K_2` reconciliation must be invoked to show the surviving class is
  a coboundary after all.  Possibility (a) is the likely one and is a
  finite-subgroup-stability statement, the cleanest the far sector has
  reduced to; it is the next thing to write.
- **The E_3 obstruction is a spectral-mass quantity the regular trace
  fights (2026-08-21).**  Finite-subgroup stability does NOT apply
  directly: `u` is unipotent, so its order-`3` action on the cube-root
  eigenspace `E_3` is an approximation artifact, not a genuine finite
  subgroup.  The right lever is the trace.  For the regular trace of
  `SL_2(Z[1/2])`, `tau(u^k) = 0` for all `k != 0`, so the spectral
  measure of `pi(u)` tends to LEBESGUE on the circle -- which has NO
  atoms.  The cube-root positions (and each fixed `3`-primary root)
  therefore carry vanishing spectral mass, so `e'`'s component on
  `E_3` contributes `<= sqrt(dim E_3 / d)` to normalized HS, which
  tends to `0` provided the `3`-primary eigenspace is a vanishing
  dimension fraction.  So the obstruction is real only if the exact
  `LV` base order `N` has a `3`-primary part `3^(v_3(N))` that is a
  non-vanishing fraction of `N`.  The genuine remaining question is
  thus purely arithmetic-analytic: does `LV`-exactification of the
  Lebesgue-spectrum unipotent keep `3^(v_3(N)) = o(N)` (equivalently
  keep the `3`-adic valuation of the order sub-logarithmic)?  The
  trace pushes toward yes (no atoms means no concentration on the
  sparse `3`-primary roots), but the `LV` rounding could in principle
  pile refinement onto the `3`-primary tower.  This is the honest
  bottom of the cascade: a competition between the atomless limiting
  spectrum and the `3`-adic valuation of the rounded order -- the
  first fully arithmetic form the residual has taken, and the exact
  statement to settle next.
- **The sharp fixed part (order-3 roots) is KILLED; residual is the
  graded 3-power tower (2026-08-21).**  Refine the fixed locus.  `x4`
  fixes a root of unity `zeta` iff `zeta^4 = zeta` iff `zeta^3 = 1` --
  ONLY the order-`3` roots `{1, omega, omega^2}`.  On order-`9` roots
  `x4` already has order `3` (`4, 7, 1 mod 9`), so it is NOT the
  identity there, and `(x4 - 1)` is invertible on the primitive
  order-`9` part; likewise every higher `3`-power level.  So the
  strictly UNABSORBABLE locus (`psi_* - 1 = 0` exactly) is the sparse
  three-point set `{1, omega, omega^2}`, a FIXED finite set.  Under
  the regular trace the spectral measure of `pi(u)` tends to Lebesgue,
  which gives each of these three points mass `0`; the exact base
  `R_0`, being HS-close, has order-`3` eigenspace dimension fraction
  `-> 0`, so `e'`'s component there is normalized-HS negligible.  The
  sharpest piece of the crux -- `e'` on the primitive cube roots --
  therefore DIES by the atomless trace.  What remains is only the
  graded `3`-power tower (orders `9, 27, ...`): there `(psi_* - 1)` is
  invertible but with gap `~ j/3^(k-1)` shrinking up the tower, so the
  residual is exactly the cascade-convergence competition
  (peeled residual size vs shrinking gap) restricted to the
  `3`-power sub-tower -- a measure-`0`-limiting, dense-but-thin set
  whose mass the trace also suppresses.  Net: the crux is no longer a
  hard fixed-point obstruction but a graded convergence on a
  trace-thin sub-tower, strictly weaker than where it stood an hour
  ago.
- **The convergence mechanism: near the identity, mass thins as fast
  as the gap (2026-08-21).**  The shrinking gap is not special to `3`;
  it is the general near-identity phenomenon.  For an eigenvalue
  `zeta` at distance `rho` from `1`, the `x4` displacement is
  `|zeta^4 - zeta| = |zeta||zeta^3 - 1| ~ 3 rho`, so the peeling gap
  scales LINEARLY in `rho`.  Crucially, under the regular trace the
  limiting spectral measure is EXACTLY Lebesgue (all moments
  `tau(u^k) = 0`), so the spectral mass in the annulus at distance
  `~ rho` from `1` is `~ rho` (arc length) -- it also thins linearly.
  Group the eigenvalues into dyadic annuli `rho in [2^{-(j+1)},
  2^{-j}]`: the gap is `~ 2^{-j}` and the mass fraction is `~ 2^{-j}`.
  If the defect `e'` restricted to an annulus has normalized-HS norm
  proportional to that annulus's MASS times the global defect `delta`,
  the per-annulus absorption cost is
  `(mass * delta)/gap ~ (2^{-j} delta)/2^{-j} = delta`, and summing
  over the `~ log(1/delta)` resolvable scales gives total
  `~ delta log(1/delta) -> 0`, dimension-free.  So the cascade
  converges PROVIDED the near-identity defect scales as annulus mass,
  not as its square root.
- **The last exponent, stated exactly.**  `||e'|_annulus||_2` is
  `sqrt(mass) * (local defect density)`; convergence needs the local
  defect density in the near-identity annuli to itself carry a
  `sqrt(mass)` factor (equivalently, the defect is not uniform but
  concentrates away from the identity in proportion to mass).  This is
  a regularity statement about WHERE the Weyl-relation defect sits
  spectrally: does it avoid the near-identity (near-`1`) band in
  proportion to the vanishing mass there?  The regular trace makes the
  mass vanish there; whether the defect vanishes at the matching rate
  is the single remaining analytic exponent.  If yes,
  `||c||_2 ~ delta log(1/delta)` and lemma (b) -- and with it the
  skeleton gluing, the far sector, and the goal along the Iwahori
  route -- closes.  This is the complete reduction: everything is
  proved or arithmetic except this one near-identity regularity
  exponent.
- **The exponent-saving mechanism, and its precise gap (2026-08-21).**
  There is a structural reason to expect the defect density to VANISH
  near the identity eigenvalue, which is exactly the `mass` (not
  `sqrt(mass)`) scaling that closes the cascade.  At the exact
  eigenvalue `1` of `V = pi(u)`, the sub-representation has
  `pi(u) = 1`, so it factors through `SL_2(Z[1/2]) / <<u>>`; but a
  unipotent NORMALLY GENERATES `SL_2(Z[1/2])` (which is perfect and
  boundedly elementary-generated), so that quotient is TRIVIAL and
  every relation -- including Weyl-torus -- holds exactly there:
  `e' = 0` at `rho = 0`.  By the bounded-width normal generation, the
  almost-version would give `||e'|| <~ rho` on the near-`1` band,
  hence density `~ rho`, hence
  `||e'|_ann||_2^2 = mass * density^2 ~ rho * rho^2 = rho^3` and
  `sum_ann rho^3 / rho^2 = sum rho < infinity` -- the cascade
  converges and lemma (b) closes.
- **The gap in that mechanism, stated exactly.**  The forcing
  `near-1 => near-trivial` is pointwise in the GROUP (each `g` is a
  bounded product of conjugates of `u^{+-1}`), but the near-`1`
  spectral BAND of `V` is NOT invariant under those conjugating
  elements `w_i` -- `pi(w_i)` mixes the band with the rest of the
  space -- so the pointwise forcing does not transfer directly to the
  `V`-eigenband, and within the skeleton `<u,h>` the band only sees
  `BS(1,4)/<<u>> = Z`, which constrains nothing.  The precise open
  statement is therefore: does the Weyl-relation defect `e'`, an
  element of `{V}'` block-diagonal in the `V`-spectrum, inherit
  `||e'|_(rho-band)|| <~ rho` from the group-level near-triviality
  DESPITE the band not being conjugation-invariant?  This is a
  commutator-mixing estimate -- how much `pi(w_i)` moves the near-`1`
  band -- and it is the single remaining analytic exponent of the
  entire `SL_2` far sector: prove it and the goal closes along the
  Iwahori route; the whole rest of the chain is proved or arithmetic.
- **The band bound is a self-similar renewal exponent under `x4`
  (2026-08-21).**  The defect satisfies `e' = c psi(c)^{-1}` with
  `psi = Ad(h)` the `x4` spectral scaling, so `Ad(h)` maps the
  `rho`-band of `V` to the `4rho`-band and relates `e'` there to `e'`
  on the `rho`-band by construction.  Hence the profile
  `m(rho) = ||e'|_(rho-band)||_2` obeys a RENEWAL/self-similarity
  relation across the geometric scales `rho, 4rho, 16rho, ...`:
  `m` at one scale is a fixed linear image of `m` at the next plus the
  local relator-defect input.  Its near-`0` behavior is therefore a
  POWER LAW `m(rho) ~ rho^alpha`, with `alpha` the leading exponent
  of the associated transfer operator on the near-identity band (the
  same `x4` self-similarity the dyadic winder draws).  Convergence of
  the cascade is exactly `alpha >= 1` (mass scaling); `alpha = 1/2`
  would be the failure.  So the last analytic question is not an
  opaque estimate but the SIGN of `alpha - 1` for one explicit
  transfer operator built from `Ad(h)`, the swap, and the boundary
  condition `e'(0) = 0` (from unipotent normal generation).  The
  boundary condition forces `alpha > 0`; whether the `x4`-expansion
  pushes it to `alpha >= 1` is the computable crux -- a spectral-radius
  sign, the cleanest and most concrete form the entire far sector has
  reached.
- **Explicit solution and the transfer computation (2026-08-21).**
  The block recursion `c_theta = e'_theta psi_theta(c_(4theta))` from
  `c psi(c)^{-1} = e'` (`psi = Ad(h)`, `h` sends `H_theta -> H_(theta/4)`)
  solves EXPLICITLY: `c_theta` is the transported product of the defect
  along the forward `x4`-orbit `theta -> 4theta -> 16theta -> ...` out
  to the `O(1)` bulk, `~ log_4(1/theta)` terms.  Then
  `||c||_2^2 = sum_theta mass_theta |c_theta - 1|^2
   <= log(1/delta) sum_k sum_theta mass_theta |e'_(4^k theta)|^2`.
  The inner sum is the transfer operator: because `x4` EXPANDS
  (`theta -> 4theta`) it contracts the spectral measure by `4^{-k}`
  per backward step, so `sum_theta mass_theta |e'_(4^k theta)|^2
   ~ 4^{-k} ||e'||_2^2`, and `sum_k 4^{-k} = 4/3` gives
  `||c||_2 <~ delta sqrt(log(1/delta)) -> 0`, DIMENSION-FREE and with
  NO exponent assumption -- the geometric `4^{-k}` from the expanding
  dynamics does the work the profile exponent was meant to.
- **The one honest gap in that computation, now mild.**  The
  contraction `sum_theta mass_theta f(4^k theta) ~ 4^{-k} integral f`
  replaces the empirical `V`-spectrum by Lebesgue at scale
  `4^{-k}` -- i.e. it needs the unipotent spectrum to EQUIDISTRIBUTE
  at the finest dyadic scale, whereas the regular trace
  (`tau(u^m) = 0`) gives Lebesgue only weakly (fixed scales).  So the
  residual is a QUANTITATIVE equidistribution RATE for `pi(u)`.  But
  the geometric `4^{-k}` weighting sets a LOW bar: any polynomial
  equidistribution rate `|empirical - Lebesgue|(scale eps) <~ eps^beta`
  with `beta > 0` makes the corrected sum
  `sum_k 4^{-k}(1 + (4^k/N)^{-beta}...)` still converge, because the
  error only bites at the finest `k ~ log_4 N` where `4^{-k} ~ 1/N`
  is already negligible.  So lemma (b) closes given ANY power-rate
  equidistribution of the unipotent spectrum -- which the exact
  moment-vanishing `tau(u^m) = 0` (all `m`) supplies via a standard
  Erdos--Turan / large-sieve bound.  This is no longer a delicate
  exponent sign but a routine equidistribution estimate; it is the
  last step, and it is a mild one.
- **Correct framework: this is the x4 cohomological equation; obstruction is Livsic periodic-orbit data (2026-08-21).** Correcting the measure-contraction optimism: in the ultraproduct V has diffuse Lebesgue spectrum and psi=Ad(h) is the KOOPMAN operator of the x4 map; a mixing expanding map has Lebesgue spectrum reaching 1, so (1-psi) has NO spectral gap. Thus c psi(c)^{-1}=e' IS the cohomological equation c - c o (x4) = e' for x4, solvable (Livsic) iff e's sums over periodic orbits vanish - and the periodic orbits of x4 are exactly the ROOTS OF UNITY. That is why roots of unity and 4-1=3 governed the whole lane: they are the periodic-orbit spectrum. Residual = Livsic periodic-orbit obstructions of the Weyl defect e' for x4; e' is HS-small, boundary e'(0)=0 kills the fixed-point obstructions, Livsic needs Holder + vanishing periodic sums. Honest final form, not a free bound.
- **Periodic orbits = cycle holonomies; the bridge to dynamics
  (2026-08-21).**  A period-`L` orbit of `x4` on the circle is a root
  of unity of order dividing `4^L - 1` (`L=1`: `3`; `L=2`: `15=3.5`;
  `L=3`: `63=9.7`), and the Livsic sum of `e'` around it is precisely
  the CYCLE HOLONOMY that opened the cascade -- the two descriptions
  coincide, closing the loop.  So the entire route reformulates the
  existence of a non-hyperlinear group as a LIVSIC RIGIDITY statement
  for the expanding map `x4`: the Weyl defect `e'` must be an `x4`
  coboundary, equivalently its holonomy vanishes around every
  `x4`-cycle (order `4^L - 1` roots), the `L=1` (order-`3`) case
  already killed by the boundary condition.  This is a genuine bridge
  from hyperlinearity to smooth-dynamics / thermodynamic formalism.
  Two structural aids for the residual: the Steinberg syzygy already
  reduced the family to ONE holonomy per cycle, and `e'` being
  HS-`delta`-small means the holonomies are `O(delta)` -- so the
  Livsic obstruction is not whether they vanish exactly but whether
  the exact-representation closure forces them below the coboundary
  threshold uniformly.  The final target is thus: the cycle-holonomy
  (periodic-orbit) invariants of the Weyl defect for `x4`.
- **Both Livsic ingredients are named and standard: RPF gap + uniform
  Gowers--Hatami (2026-08-21).**  Two realizations complete the
  architecture.  (1) VANISHING periodic sums.  A period-`L` `x4`-cycle
  carries `V` of order `4^L - 1` (odd, so `2` is a unit) together with
  `h` (= `x4`) and the swap `s`; the relations `h V h^{-1} = V^4`,
  `s h s^{-1} = h^{-1}`, `s V s^{-1} = V^{-1}` are exactly those of a
  finite congruence quotient `SL_2(Z/(4^L - 1))`.  So each cycle carries
  an APPROXIMATE `SL_2(Z/(4^L-1))`-representation, and Gowers--Hatami
  finite-group HS-stability -- with an ABSOLUTE, group-independent
  constant -- puts it `O(delta)`-close to an EXACT one, where the
  Weyl-torus relation holds exactly.  Hence every periodic-orbit
  (cycle-holonomy) sum of `e'` is `O(delta)`, uniformly in `L`: the
  Livsic obstruction vanishes to first order.  (2) BOUNDED coboundary.
  The earlier `no spectral gap` worry was about the KOOPMAN operator
  (composition with `x4`) on `L^2`, which indeed has Lebesgue spectrum
  to `1`.  But the coboundary is solved by its ADJOINT, the RUELLE
  TRANSFER operator (sum over the four `x4`-preimages, each contracting
  by `1/4`), which by Ruelle--Perron--Frobenius HAS a spectral gap on
  Holder functions.  So given vanishing periodic sums and Holder `e'`,
  the coboundary `c` exists with `||c|| <~ ||e'||_(Holder)`,
  geometrically -- no `L^2` gap needed.  The residual is now exactly
  two standard inputs: uniform Gowers--Hatami across the family
  `{SL_2(Z/(4^L-1))}` (giving vanishing periodic sums to `O(delta)`)
  and Holder regularity of the Weyl defect `e'` in the `V`-spectral
  variable (for RPF).  Both are of the expected-true kind; writing
  them is the remaining work, and the framework -- Livsic + RPF +
  Gowers--Hatami for the `x4` map -- is now fully assembled.
- **Ingredient (1) sharpened: dihedral GH, and the L-uniformity is the
  real point (2026-08-21).**  Scrutinizing (1): the cycle block does
  NOT satisfy the congruence relations of `SL_2(Z/(4^L-1))` -- the
  microstate only obeys the `SL_2(Z[1/2])` relations, and congruence-
  kernel elements go to trace-`0`, not near `1`.  So GH applies not to
  the full finite group but to the DIHEDRAL cycle-structure
  `<h, s | s h s^{-1} = h^{-1}>` acting on the `x4`-cycle (and its
  `s`-image, the inverse cycle): crucially `s h s^{-1} = h^{-1}` is an
  EXACT `SL_2(Z[1/2])` relation, satisfied to `O(delta)`, and `h^L` is
  `x4^L = id`-scalar on the cycle, so `<h,s>` restricts to an
  `O(delta)`-approximate finite dihedral representation there.  GH then
  gives an exact dihedral rep `O(delta)`-close, in which the Weyl-torus
  relation is exact -- the periodic-orbit obstruction to first order.
  The genuine remaining subtlety is UNIFORMITY IN `L`: the naive
  periodic sum telescopes as `O(L delta)`, which is not uniformly small
  for long cycles.  This is exactly what the thermodynamic weighting in
  Ruelle--Perron--Frobenius handles -- long `x4`-orbits carry
  exponentially small measure/pressure weight `~ 4^{-L}`, so the
  measure-weighted periodic-sum contribution is `~ L delta * 4^{-L}`,
  summable over `L` with total `O(delta)`.  So the two ingredients
  interlock: RPF supplies both the Holder coboundary bound AND the
  orbit weighting that tames the `O(L delta)` growth of the GH periodic
  sums.  The residual is therefore a single quantitative statement --
  the RPF-weighted sum `sum_L (orbit count)_L * L delta * 4^{-L}` over
  the `x4` periodic orbits converges (it does: orbit count `~ 4^L/L`,
  so the sum is `sum_L delta = ...` -- NEEDS the count/weight balance
  checked exactly, `4^L/L * L * 4^{-L} = 1` per `L`, giving
  `sum_L delta` which DIVERGES in `L`).  So the crude weighting is NOT
  enough; the true control must use that the DEFECT itself decays along
  orbits (Holder + `e'(0)=0`), not just the measure weight.  Honest
  status: ingredient (1) reduces to a defect-decay-vs-orbit-count
  balance, the same Holder regularity of `e'` that ingredient (2)
  needs -- so BOTH residual inputs collapse to ONE: Holder regularity
  of the Weyl defect in the `V`-spectral variable.  That single
  regularity statement closes the far sector.
- **The regularity needed is a TRACE seminorm, not pointwise Holder
  (2026-08-21).**  Pointwise Holder regularity of `e'` is not free: a
  general microstate has no spectral regularity, and after
  exactification only the Weyl `s` is rough, which alone gives no
  `theta`-continuity across `V`-eigenspaces.  But the coboundary does
  not need pointwise Holder.  The Ruelle transfer operator has the
  Lasota--Yorke form: its spectral gap holds already on functions of
  BOUNDED VARIATION / fractional Sobolev regularity, measured by the
  dynamical seminorm `|| e' - psi(e') ||_2`.  Crucially this seminorm
  is a TRACE quantity: `psi = Ad(h)`, so
  `|| e' - psi(e') ||_2^2 = tau(| e' - h e' h^{-1} |^2)` -- the trace
  of an explicit word in the microstate, NOT a pointwise spectral
  condition.  So the last lemma becomes: the Weyl defect `e'` has
  small dynamical Sobolev seminorm `|| e' - h e' h^{-1} ||_2 <~ delta`.
  This is genuinely trace-accessible, and plausibly `O(delta)` because
  `e'` is itself the `O(delta)` defect of a relation and `h e' h^{-1}`
  is its transport under an EXACT tower automorphism -- their
  difference is a second-order defect (the failure of `e'` to be
  `h`-covariant, which the exactness of the `h`-tower controls).  So
  the far sector closes via Lasota--Yorke RPF given
  `|| e' - h e' h^{-1} ||_2 <~ delta`, a computable trace bound
  replacing the pointwise-Holder lemma.  This is the sharpest exit:
  the last input is one trace inequality on the microstate.
- **Correction: the dynamical seminorm is trivially small but is the
  WRONG one (2026-08-21).**  Testing the trace bound immediately:
  `|| e' - psi(e') ||_2 = || [e', h] ||_2 <= 2 || e' - 1 ||_2 <= 2 delta`
  trivially, because a near-identity `e'` approximately commutes with
  every unitary.  But this dynamical (`x4`-orbit-direction) seminorm is
  NOT what the Ruelle/Lasota--Yorke gap needs: the transfer operator
  acts in the SPATIAL (`theta`) variable and its gap requires variation
  in `theta` (transverse to orbits), which the orbit-direction bound
  does not supply.  Equivalently, in the Koopman picture the L^2
  cohomological equation `c - c circ (x4) = e'` is solvable with
  control iff `sum |hat e'(lambda)|^2 / |1 - lambda|^2 < infinity`
  against the (Lebesgue, a.c.) spectral measure of the mixing Koopman
  operator -- a genuine condition on the spectral DENSITY of `e'` at
  eigenvalue `1`, not implied by `|| e' ||_2 = delta`.  So the trace-
  seminorm-for-free hope is closed off honestly: the last input is a
  real spectral-density regularity of the Weyl defect at Koopman-`1`
  (equivalently `theta`-variation), the same regularity flagged before,
  now confirmed genuine.  This route is a complete architecture --
  skeleton, rigidity, syzygy, prime-3, order-3 kill, Livsic, RPF,
  dihedral GH -- modulo exactly this one frontier regularity theorem
  for the Weyl defect.  The next real attack is to control that
  spectral density from the microstate structure (bounded elementary
  generation giving `theta`-Lipschitz variation of the defect), which
  is the genuine hard core the whole chain isolates.
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
