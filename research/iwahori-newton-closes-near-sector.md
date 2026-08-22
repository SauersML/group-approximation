---
rg: 2
id: iwahori-newton-closes-near-sector
kind: claim
title: Uniform infinitesimal rigidity gives a linear error bound inside each fixed torsion-multiplicity stratum
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that is the first-order cocycle gap; this integrates it on one smooth multiplicity stratum and records why the union of strata is not yet covered.
---

Let `F` be the Iwahori compatibility map on pairs of exact modular
representations and let `C=F^(-1)(0)` be the compatible locus.  Fix the
multiplicities of every order-two and order-three eigenvalue in both modular
vertices.  This defines a smooth product of compact flag manifolds.

**ESTABLISHED on this stratum.**  If `sigma_0` is the dimension-free lower
singular-value constant from `iwahori-uniform-infinitesimal-rigidity`, there
are dimension-free `L,r_0>0` such that every pair `pi` whose nearest
compatible point `pi~` lies in the same stratum and whose stratum distance
is below `r_0` satisfies

```text
D(pi) <= (2/sigma_0) def(pi).                            (NR1)
```

Indeed, a minimizing geodesic from `pi~` to `pi` is normal to `C` inside
the stratum.  The differential `DF(pi~)` is bounded below by `sigma_0` on
that normal space.  Since `F` is made of fixed unitary words, its second
derivative has a dimension-free bound `L`.  Taylor's formula gives

```text
def(pi) >= sigma_0 D(pi)-(L/2)D(pi)^2,
```

and `(NR1)` follows when `D(pi)<=sigma_0/L`.  This uses a lower bound on the
normal derivative; it does not incorrectly assume that the overdetermined
mismatch derivative is surjective.

**Remaining near-sector issue.**  This is not yet a uniform tube theorem on
the union of all multiplicity strata.  Changing one order-two or order-three
eigenvalue block costs only `O(d^(-1/2))` in normalized Hilbert--Schmidt
distance, so distinct strata approach each other as `d` grows.  A complete
near-sector theorem must reconcile these small-rank stratum changes while
remaining in the same matrix dimension (or explicitly account for flexible
padding).  The far outlier sector remains separate as well.

## Attempts

- **DEMOTED TO OPEN (2026-08-21 adversarial audit).**  The sentence "its
  second derivative has a dimension-free bound `L`" in normalized
  Hilbert--Schmidt norm is false:
  `normalized-hs-taylor-remainder-is-not-dimension-free` (rank-one
  anti-Hermitian `X` with eigenvalue `i pi` has
  `|| X^2 ||_2 / || X ||_2^2 = sqrt d`), and it invalidates the route.  The
  correct second-order bound is `|| F''[X,X] ||_2 <= L || X ||_op || X ||_2`,
  so the Taylor step closes only under an operator-norm proximity
  hypothesis `|| X ||_op <= sigma_0 / (2L)`; that version is true but is
  not the HS-metric near sector that `iwahori-local-global-defect-question`
  consumes.  The rank-one direction is a rotation of a single flag line
  inside a fixed torsion-multiplicity stratum, so the stratum restriction
  does not avoid it; the stratum-reconciliation issue recorded above is a
  second, independent gap.  `(NR1)` in the HS metric is therefore OPEN.

