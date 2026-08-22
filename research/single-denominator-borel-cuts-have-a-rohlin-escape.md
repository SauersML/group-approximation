---
rg: 2
id: single-denominator-borel-cuts-have-a-rohlin-escape
kind: claim
title: One denominator self-similarity admits trace-one-over-forty-two Rohlin cuts
distinct_from:
  fixed-spherical-polynomials-have-no-42nd-projection: That rules out every fixed finite-depth polynomial; this allows depth to grow and proves that one amenable denominator action then has asymptotically invariant polynomial cuts.
  regular-congruence-depth-mixtures-remain-folner: That constructs Folner profiles in the discrete conductor-depth marginal; this gives the measure-theoretic projection and polynomial approximation theorem on any diffuse invariant abelian conductor algebra.
  six-parahoric-finite-fiber-folds-remain-amenable: That treats finite-fiber coweight graphs; this isolates the still simpler obstruction that one denominator automorphism can never have a strong-ergodicity gap.
---

# One denominator self-similarity admits Rohlin cuts

Let `(X,mu)` be a diffuse standard probability space and let `T` be an
aperiodic probability-preserving automorphism.  Put `alpha=1/42`.  There are
projections `e_m in L^infinity(X)` such that

```text
|tau(e_m)-alpha|=O(1/m),
||T(e_m)-e_m||_2=O(m^(-1/2)).                            (RBC1)
```

Indeed, take a Rohlin tower of height `m` covering all but `o(1/m)` of the
space and let `e_m` be the union of `floor(alpha m)` consecutive levels.
Only the bottom and top levels contribute to the symmetric difference, so

```text
mu(T(E_m) symmetricDifference E_m)=O(1/m),              (RBC2)
```

which is `(RBC1)` after taking a square root.

Suppose now that a unital self-adjoint polynomial algebra `A_0` is dense in
`C(X)` (or is `L^2`-dense with uniformly contractive approximants).  For each
`m` one can choose a self-adjoint contraction `f_m in A_0` with

```text
|tau(f_m)-alpha| ->0,
||f_m^2-f_m||_2 ->0,
||T(f_m)-f_m||_2 ->0.                                   (RBC3)
```

First approximate `1_(E_m)` in `L^2` by a continuous `[0,1]`-valued
function, then uniformly by a polynomial.  The contraction bound transfers
the idempotence defect, and

```text
||T(f_m)-f_m||_2
 <=2||f_m-e_m||_2+||T(e_m)-e_m||_2.                     (RBC4)
```

In finite matrices, spectral rounding of `f_m` at `1/2` gives an actual
projection with the same limiting trace and covariance estimates.

## Arbitrary polynomial-cost growth can be diagonalized

Let `A_m<infinity` be any propagation constant for evaluating the fixed
polynomial `f_m` on a presentation assignment of defect `delta`; no bound on
the growth of `A_m` is assumed.  Choose a decreasing sequence `delta_m` with

```text
delta_m A_m <=1/m,
```

and let `m(delta)` tend to infinity slowly enough that
`delta A_(m(delta))->0`.  Combining `(RBC3)` with ordinary word telescoping
then makes both polynomial approximation error and presentation-propagation
error vanish.  Thus exponential, superexponential, or otherwise bad finite
degree constants do not by themselves obstruct a qualitative normalized-HS
argument; a staircase always outruns them.

## Arithmetic consequence and scope

If one denominator element of `SL_3(Z[1/2])` preserved a diffuse abelian
conductor algebra containing the desired source projection, its induced
automorphism could not supply a dimension-independent covariance gap.  The
cuts above would realize the required trace asymptotically while paying
vanishing section energy.  A single doubling/shift self-similarity is
therefore an amenable escape, not a renormalization engine.

This is conditional: conjugation by the denominator need not preserve the
regular spherical Hecke algebra as an ordinary matrix-coordinate algebra,
and a Hecke spectral projection may live on Hilbert--Schmidt space rather
than be left multiplication by a matrix projection.  Those failures are now
the useful possible obstruction.  A successful arithmetic proof must show
that no common invariant conductor algebra exists, or use several
Weyl-conjugate denominator actions whose joint equivalence relation has a
uniform spectral/strong-ergodicity gap and whose cuts are authenticated on
the same matrix carrier.
