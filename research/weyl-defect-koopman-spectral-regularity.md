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
