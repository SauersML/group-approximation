---
rg: 2
id: weyl-defect-koopman-spectral-regularity
kind: claim
title: The Weyl defect has controlled Koopman spectral density at eigenvalue one
distinct_from:
  solenoid-absorption-cascade-converges: that assembles the Livsic/RPF/Gowers-Hatami machine and consumes this as its single remaining analytic input; this is that input, isolated as a first-class hole.
  bs14-exact-representation-variety-is-hs-locally-rigid: that is the proved local rigidity aligning exact skeletons; this is the transverse spectral regularity of the residual Weyl defect, a different quantity.
  skeleton-relative-hs-stability-for-sl2: that is the gluing endpoint; this is the one analytic lemma the gluing's cascade reduces to.
---

Let `pi` be an accurate finite-dimensional approximate representation
of `SL_2(Z[1/2])` with the parabolic skeletons already exactified
(`bs14-exact-representation-variety-is-hs-locally-rigid`), `V = pi(u)`
the exact odd base, and `e'` the residual Weyl-torus relation defect
(the failure of `s h s^{-1} = h^{-1}`) projected into the base
commutant `{V}'`.  Let `U_T` be the Koopman operator on
`L^2({V}', tau)` of the `x4` spectral map `T` (`= Ad(h)`).  CLAIM:
there are dimension-free constants such that

```text
sum_lambda | hat e'(lambda) |^2 / | 1 - lambda |^2  <=  C delta^2,   (KSR)
```

the sum over the (Lebesgue, absolutely continuous) Koopman spectrum,
where `delta` is the microstate relator defect.  Equivalently, `e'`
has `theta`-Lipschitz (finite bounded-variation) spectral profile in
the `V`-eigenvalue variable transverse to the `x4`-orbits, with
seminorm `O(delta)`.

By `solenoid-absorption-cascade-converges` (its Livsic + Ruelle--
Perron--Frobenius + dihedral Gowers--Hatami assembly), `(KSR)` yields
the coboundary `c` with `|| c ||_2 <= C' delta`, closing the skeleton
gluing, the far sector, and -- through
`common-odd-model-from-skeleton-relative-stability`,
`odd-congruence-vertex-sector-admits-no-exact-leak`, and the Iwahori
route -- the goal.

## Fixed-regular split: the obstruction is free, only regular-sector BV remains

Linearize the coboundary as `(1 - psi) c = phi`, `phi = delta e'`,
`psi = Ad(h)` on `Z = {V}'`, and split
`Z = Z^psi (+) (Z^psi)^perp` where `Z^psi = {V,h}'` is the tower
MULTIPLICITY algebra.

- **The fixed-algebra obstruction is automatically `O(delta)`.**
  Solvability in `L^2(Z)` requires `phi` orthogonal to `ker(1-psi) =
  Z^psi`, i.e. `E_(Z^psi)(phi) = 0`.  But `E_(Z^psi)(phi)` is a
  COMPONENT of `phi`, so `|| E_(Z^psi)(phi) ||_2 <= || phi ||_2 <=
  delta` with no regularity input at all.  The un-removable part of
  the defect is therefore `O(delta)` and lives entirely in the
  multiplicity algebra, where it is an `O(delta)` residual, not an
  obstruction to an `O(delta)` coboundary.
- **On the regular sector `psi` is fixed-point-free, so RPF applies.**
  `(1 - psi)` is injective on `(Z^psi)^perp` (no invariant vectors
  there by definition).  The coboundary is built by the Ruelle
  transfer operator `L` (adjoint of the Koopman `psi`), which by
  Ruelle--Perron--Frobenius has a spectral gap on the mean-zero part:
  `c = sum_(n>=0) L^n phi_0` with `phi_0 = phi - E_(Z^psi)(phi)`
  converges geometrically, `|| c ||_2 <= C || phi_0 ||_2 <= C delta`,
  PROVIDED `phi_0` lies in the RPF regularity space.
- **So the entire residual is: BV-regularity of the mean-zero Weyl
  defect `phi_0` on the regular sector.**  This is strictly cleaner
  than the earlier "spectral density at Koopman-1" form: the singular
  (`|1-lambda|^{-2}`) blow-up is confined to the fixed algebra `Z^psi`,
  where it is already handled by the free `O(delta)` bound; on the
  complement the RPF gap does the work.  The one remaining question is
  whether the noncommutative RPF regularity space is the SPATIAL
  variation (transverse, the hard direction) or admits a DYNAMICAL /
  algebraic seminorm that the relator structure controls -- the next
  technical point, below.

## The precise crux: a Wasserstein-vs-HS norm mismatch

Push the regular-sector solve to its exact functional-analytic core.
Represent the abelian component of the mean-zero defect as a complex
measure `nu = g(theta) d mu_V(theta)` on the `V`-spectrum, where
`g(theta)` is the `theta`-diagonal of the Weyl defect.  Then:

- `nu` is AUTOMATICALLY small in total variation:
  `|| nu ||_TV = | nu |(circle) <= || e' ||_1 = O(delta)`.
- The coboundary equation is `nu = mu - T_* mu` (`T = x4`), and the
  Ruelle transfer operator for the expanding map `x4` DOES contract --
  but in WASSERSTEIN / dual-Holder norm (the standard exponential-
  mixing statement for expanding maps), NOT in total variation and NOT
  in HS.  So RPF delivers a coboundary `mu` with `|| mu ||_Wass <=
  C || nu ||_Wass <= C delta`.
- But the coboundary `c` the cascade needs must be small in HS /
  `L^2` operator norm, and Wasserstein-small does NOT give HS-small.

So the genuine, isolated obstruction is a NORM MISMATCH: the transfer
operator's spectral gap lives in Wasserstein (where the defect is free)
while the required coboundary bound is in HS (where regularity is not
free).  This is sharper and more attackable than "spectral density at
`1`" or "BV regularity": it is the specific question of upgrading a
Wasserstein coboundary bound to an HS one for the `x4` transfer
operator, which is an interpolation / a-priori-estimate problem about
one explicit expanding map, and it is exactly where the frontier now
sits.  Candidate upgrades: (i) the defect has extra structure (it is a
RELATOR defect, a bounded word) that may force HS `pprox` Wasserstein
on it; (ii) an elliptic-type a-priori estimate for `1 - T_*` on the
regular sector using the tower multiplicity as ellipticity.

## Exact Fourier solution of the coboundary; the crux is one trace sum

Solve the abelian coboundary `(1 - L) g = nu` (`L` = Ruelle operator of
`x4`) explicitly in Fourier modes on the `V`-spectrum.  `L` acts as a
weighted downward shift: `(Lg)^_m = g^_(4m)`, so
`g^_m - g^_(4m) = nu^_(m)`, which solves EXACTLY

```text
g^_m = sum_(n>=0) nu^_(4^n m)      (forward x4-orbit of frequency m).
```

Each Fourier moment is a WORD TRACE: with `R = s h s^{-1} h` the Weyl
relator and `u` the unipotent (`V = pi(u)`),

```text
nu^_(k) = tau(e' V^{-k}) = tau_micro(R u^{-k}).
```

Hence the HS norm of the coboundary `c` is EXACTLY

```text
|| c ||_2^2  =  sum_m | sum_(n>=0) tau_micro(R u^{-4^n m}) |^2,     (TS)
```

and the ENTIRE frontier is the single trace-summability statement
`(TS) = O(delta^2)`.

- **Why this is genuinely attackable.**  `(TS)` is not abstract
  rigidity: it is an explicit sum over the explicit words
  `R u^{-4^n m}`.  Each term `tau_micro(R u^{-k})` tends to
  `tau_reg(R u^{-k}) = 0` (the word is nontrivial in the free/HNN
  group), and the frequencies `4^n m` are geometrically sparse.  The
  question is purely the RATE: does the microstate trace of these
  growing words vanish fast enough for the double sum to be
  `O(delta^2)`?  This is a quantitative-mixing / large-sieve estimate
  for the microstate along one lacunary (`x4`) frequency family, and it
  is the sharpest and most concrete form the whole non-hyperlinearity
  program has reached.
- **The lacunary structure is favorable.**  The inner sum runs over the
  lacunary set `{4^n m}`; lacunary Fourier sums obey strong
  (Sidon / large-sieve) bounds, so `|sum_n tau_micro(R u^{-4^n m})|` is
  controlled by an `ell^2` norm of the individual moments rather than
  their `ell^1`, and the outer `sum_m` then telescopes across
  `x4`-orbits of frequencies with the geometric `4`-sparsity providing
  convergence.  Making this rigorous -- a lacunary large-sieve bound on
  the microstate word-traces -- is the exact next step, and it is a
  concrete harmonic-analysis computation on one explicit word family.

## Corrected exact formula: the coboundary norm is a cycle-discrepancy

Careful redo (`x4` is a BIJECTION on `Z/N`, `N` odd, so `L` PERMUTES
Fourier modes; the earlier "full-orbit sum" was wrong).  On a
`x4`-cycle `C = (m_0, m_1 = 4 m_0, ..., m_(L-1))`, the equation is
`g_(m_i) - g_(m_(i+1)) = nu^_(m_i)`.  Two exact consequences:

- **Solvability = Livsic.**  Summing around the cycle telescopes to
  `sum_(i) nu^_(m_i) = A_C = 0`: the coboundary exists iff every
  `x4`-cycle moment-sum `A_C` vanishes.  (`A_C = tau(e' . sum_(k in C)
  V^{-k})` is the `x4`-invariant / fixed-algebra component on `C`,
  already `O(delta)` by the free bound; in the ultraproduct
  `a_k -> 0` drives each fixed `A_C -> 0`.)
- **Exact norm = cycle discrepancy.**  When solvable, the
  `L^2`-minimal solution has

  ```text
  || c ||_2^2  =  sum_C Var_(m in C)( S_m ),
  S_m = partial sum of nu^_ around C up to m,
  ```

  the total DISCREPANCY of the moment sequence `a_k = tau_micro(R u^{-k})`
  walked around each `x4`-cycle.

So the frontier is now exactly a DISCREPANCY BOUND: the partial sums of
the Weyl-relator moments, traversed around each `x4`-cycle, have
variance summing to `O(delta^2)`.  This is a concrete equidistribution
statement about one explicit sequence (`k -> tau_micro(R u^{-k})`) under
one explicit expanding permutation (`x4` on `Z/N`), squarely in the
domain of discrepancy / Erdos--Turan theory -- the sharpest and most
standard-shaped form the whole program has produced.  The moments obey
`sum_k |a_k|^2 <= delta^2` (Parseval), so it is a variance-of-partial-
sums bound for an `ell^2`-small sequence around expanding-map cycles;
lacunarity of the `x4` orbit structure is the tool that should convert
the `ell^2` moment bound into the discrepancy bound.

## Exact low-orbit-frequency obstruction to a generic discrepancy bound

Lacunarity of the labels `m,4m,4^2m,...` does **not** by itself convert
the Parseval bound into dimension-free discrepancy.  On one `x4`-cycle
of length `L`, identify the normalized Hilbert space with
`ell^2(Z/LZ)` and let `psi` be cyclic shift.  With

```text
zeta=exp(2 pi i/L),             phi_j=delta zeta^j,
```

one has `E_(ker(1-psi))(phi)=0` and `||phi||_2=delta`.  Nevertheless the
mean-zero solution of `(1-psi)c=phi` is, up to the orientation of the
shift,

```text
c_j=delta zeta^j/(1-zeta),
||c||_2=delta/|1-zeta| >= delta L/(2 pi).              (KSR-LOW)
```

Equivalently, the partial sums around the cycle have variance of order
`delta^2 L^2`.  This is exactly a Koopman eigenmode whose eigenvalue is
the first nontrivial `L`-th root of unity, hence approaches `1` as the
cycle length grows.  It is already a diagonal element of the exact base
commutant on that cycle, so neither exactification of the `BS(1,4)`
skeleton, removal of the fixed algebra, Parseval, nor the apparent
lacunarity of the integer labels excludes it.

This calculation does not refute `(KSR)`, because it does not show that
`phi` can occur as the projected defect of the Weyl relator in a full
approximate `SL_2(Z[1/2])` tuple.  It does rule out the proposed generic
large-sieve step.  The genuinely missing arithmetic assertion is now:
the coupled Weyl and opposite-parabolic relations must suppress the
low **orbit-frequency** Fourier modes of the projected defect, uniformly
over arbitrarily long `x4`-cycles.  A proof must estimate those modes
from the remaining group relators; harmonic analysis of the exact
solenoid skeleton alone cannot give the required constant.

## Attempts

- **Why the naive bounds miss it.**  `|| e' ||_2 = delta` alone does
  not give `(KSR)`: the weight `|1-lambda|^{-2}` blows up at the
  Koopman eigenvalue `1` (the almost-`x4`-invariant modes of `e'`),
  and the mixing map has purely a.c. spectrum reaching `1`, so no
  spectral gap saves it.  The orbit-direction seminorm
  `|| e' - Ad(h)(e') ||_2 <= 2 delta` is trivially small but is the
  wrong (parallel, not transverse) direction.
- **Band-invariance attack, REFUTED at the Weyl swap (2026-08-21).**
  The tempting close: show the near-`1` band `P_rho` of `V` is
  approximately preserved by all generators, so the sub-representation
  there has `pi(u) = V ~ 1`, and bounded normal generation forces every
  `pi(g) ~ 1` on the band, hence `e'|_band ~ 0`.  Two generators
  cooperate: `V` preserves `P_rho` exactly (diagonal), and `h` CONTRACTS
  it into itself (`x4` toward `1`, so `pi(h) P_rho = P_rho pi(h) P_rho`,
  `[pi(h),P_rho]` one-sided zero).  But the Weyl `s` does NOT preserve
  the band: the correct relation is `s e_+(x) s^{-1} = e_-(-x)` (Weyl
  SWAPS upper and lower unipotents), NOT `s u s^{-1} = u^{-1}`.  So `s`
  maps the `V`-near-`1` band to the `L`-near-`1` band (`L` = lower
  unipotent, `L = s V-tower s^{-1}`), a DIFFERENT subspace.  The band is
  therefore not group-invariant, the normal-generation forcing does not
  transfer to the band, and this natural attack fails precisely at the
  Weyl swap -- confirming `(KSR)` as a genuine frontier statement, not a
  soft consequence of near-triviality.  (Recorded so the next attempt
  does not re-walk it: the obstruction is exactly that `s` exchanges the
  two towers whose near-`1` bands only partially overlap.)
- **Casimir-symmetrized band, checked and failed (2026-08-21).**  The
  band attack fails because `s` swaps the two towers; the natural fix
  is a swap-SYMMETRIC near-identity region.  `s` preserves
  `|V-1|^2 + |L-1|^2`, and the PRODUCT `theta_V . theta_L` is preserved
  by both `s` (swap) and `h` (which scales `theta_V` up by `4`,
  `theta_L` down by `4`) -- i.e. the Casimir quadratic.  A spectral
  band of an approximately-central Casimir WOULD be group-invariant and
  close the argument.  But there is NO central Casimir in the DISCRETE
  group `SL_2(Z[1/2])`: the Casimir is a Lie-algebra/enveloping-algebra
  object, and a discrete-group microstate need not be close to any
  representation extending to `SL_2(R)` or `SL_2(Q_2)`, so no
  approximately-central quadratic word exists to define the invariant
  band.  The symmetrized-band route is therefore closed off; the
  partial `V`/`L` band overlap remains the attack surface but without an
  invariant carrier from central elements.  A viable attack must
  instead control the transverse variation directly through the
  swap-transport, not via an invariant band.
- **Overlap-propagation reduces KSR to the balance points; the
  invariant coordinate is the product `P` (2026-08-21).**  `h` scales
  the `V`-part up by `4` and the `L`-part down by `4`, so the PRODUCT
  `P = |V-1| . |L-1|` is `h`-INVARIANT -- the natural coordinate on the
  `x4` dynamics, matching the trivially-small dynamical seminorm
  `|| e' - Ad(h) e' ||_2 <= 2 delta` (`e'` is nearly `h`-orbit
  constant).  Flowing a `V`-band point by `h^n` drives it to its
  BALANCE point where `V`-part ~ `L`-part ~ `sqrt(P)` in
  `n ~ (1/2) log(1/P)` steps; telescoping the per-step covariance
  defect gives

  ```text
  || e'(x) ||  <~  delta . log(1/P(x))  +  || e'(balance point) ||.
  ```

  Because `P` is `h`-invariant, `e'` is orbit-almost-constant and the
  forward-orbit sums that build the coboundary `c` integrate the log
  against `d theta` to `delta . polylog -> 0`.  So KSR on the entire
  `V`-band REDUCES to KSR at the OVERLAP (the balance points, where
  both unipotents are `~ sqrt(P)` near `1`) -- the deepest near-identity
  region, of vanishing measure.  This is a genuine localization: the
  frontier regularity only has to be established on the overlap, not
  everywhere.  The residual base case -- `e' ~ 0` at the balance point
  -- still meets the near-triviality-forcing gap (the balance region is
  not group-invariant either), so it is not free; but it is now
  confined to the smallest possible region, where both `V` and `L` are
  near `1` and the representation is genuinely near-trivial, the most
  favorable place for a normal-generation argument to finally bite.
- **Capstone: elementary forcing is exhausted; the fit tool is
  character rigidity, and it meets the shared non-amenable frontier
  (2026-08-21).**  Even the overlap `Omega` (both `V` and `L` near `1`,
  where the representation IS genuinely near-trivial) is not
  group-invariant: `u` conjugates `l` into a mixed upper/lower element
  (`e_+ e_- e_+^{-1}` has both parts), so NO near-identity region is
  group-invariant at ANY scale.  That non-abelian coordinate mixing is
  the essential reason elementary near-triviality/normal-generation
  forcing cannot establish `(KSR)` -- every invariant-band variant
  (plain band, Casimir-symmetrized, overlap) fails for the same
  structural reason.  The tool that fits is CHARACTER RIGIDITY of
  `SL_2(Z[1/2])` (Peterson--Thom), whose consequence (Dogon--
  Vigdorovich hyperfinite HS-stability) supplies the needed spectral
  regularity ON THE AMENABLE part of the commutant -- but leaves the
  NON-AMENABLE part, exactly the residual shared by
  `no-spherical-leak-in-matrix-ultraproducts`,
  `relative-commutant-collapse-for-sl2-pair`, and
  `hnn-carrier-factorial-character-collapse`.  So this far-sector route,
  fully reduced, MEETS the same non-amenable spectral-rigidity frontier
  as the RCC and carrier-character routes: they are one frontier viewed
  through different machinery.  `(KSR)` is its `x4`-dynamical face; the
  RCC spherical-leak is its Hecke face; the carrier character is its
  factorial-trace face.  Establishing any one closes the goal, and each
  is the same non-amenable rigidity.  This unifies the program's open
  routes at a single frontier statement.
- **The real attack: bounded elementary generation.**
  `SL_2(Z[1/2])` is boundedly generated by unipotents; every fixed
  generator is a bounded-length product of conjugates of `u^{+-1}`,
  so on the near-identity spectral band of `V` (where `pi(u) ~ 1`)
  every `pi(g) ~ 1` to first order, forcing the Weyl defect to vanish
  at eigenvalue `1` and vary Lipschitz-ly nearby -- exactly the
  transverse regularity `(KSR)` asks for.  The gap in the naive form
  of this argument (the near-`1` band of `V` is not conjugation-
  invariant) is precisely what `(KSR)` must overcome, quantitatively:
  bound the transverse spectral variation of `e'` by the commutator
  mixing `|| [pi(w), P_band] ||` of the bounded generating words with
  the band projections.  This is the single frontier estimate the
  entire route isolates; it is a quantitative bounded-generation /
  spectral-regularity statement about `SL_2(Z[1/2])`, self-contained
  and dimension-free.
