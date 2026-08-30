---
rg: 2
id: stw99-problem-xciv-hyperfinite-factor-separably-z-stable
kind: claim
title: The hyperfinite II1 factor is separably Z-stable (STW Problem XCIV)
root: true
distinct_from:
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that asks for finite-dimensional operator-norm approximation of R; this asks for separable Jiang--Su stability, a regularity property; both are about R and neither is known.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw99-xciv-norm-matrix-tower-audit-2026-08-30.md
  - research/artifacts/stw99-xciv-prime-dimension-drop-audit-2026-08-30.md
  - research/artifacts/stw99-xciv-single-block-diagonal-audit-2026-08-30.md
---

**Problem XCIV of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026).**  Is the hyperfinite II₁ factor `R` separably
`𝒵`-stable?

`R` is not `𝒵`-stable (all II₁ factors are tensorially prime as
C\*-algebras), and `R^ω` is separably `𝒵`-stable; the question is `R` itself.
A positive answer would follow from property (SI) for `R`, suitably adapted to
relative commutants in large ultrapowers (`stw99-xciv-from-si-for-r`), and
would allow `R` as a codomain in the classification of morphisms.

An unconditional positive subclass is now available at
`stw99-xciv-norm-matrix-tower-has-zstable-hull`: every subset approximated in
operator norm by a coherent finite-dimensional tower with uniformly growing
nonzero Bratteli tail multiplicities lies in an approximately divisible,
hence `Z`-stable, AF norm core.  The same multiplicity condition makes every
finite-stage tail commutant `Z`-stable and gives actual norm-central copies of
`Z` on finite tests.  This includes full-matrix UHF cores, but hyperfiniteness
only gives `2`-norm approximation for arbitrary elements, so the unrestricted
root remains open.

There is also an exact finite-block reformulation at
`stw99-xciv-separable-zstability-iff-local-prime-dimension-drops`.  It is
enough, and necessary, to find actual operator-norm-central unital copies of
each prime block `I_(k,k+1)` on finite tests.  Failure is therefore witnessed
by one finite set, one block, and one positive uniform commutator gap.  The
recursive proof constructs a separable hull containing the prescribed seed;
it uses the compatibility-free Toms--Winter dimension-drop absorption
criterion and makes no claim that `2`-norm centrality gives norm control.

The finite-block reformulation can be reduced to one block.
`stw99-xciv-single-prime-block-centrality-is-exact` proves that local
operator-norm central copies of the fixed algebra `I_(2,3)` are already
equivalent to separable `Z`-stability.  A triangular diagonal constructs
countably many commuting central copies in the norm sequence algebra and
therefore a central copy of `I_(2,3)^(tensor infinity)`; the Dadarlat--Toms
infinite-tensor-power theorem makes that algebra `Z`-stable.  Consequently a
negative answer to XCIV has a finite norm-gap certificate for this single
fixed block.  The argument cannot run with `2`-norm commutators, which land
only in the tracial sequence quotient.

For individual finite tests, operator-norm local finite-dimensionality is a
new positive class.  `stw99-xciv-finite-dimensional-radius-controls-block-defect`
proves that the fixed-block commutator defect is at most twice the distance
of the test tuple to a unital finite-dimensional subalgebra of `R`.  This
covers every finite tuple in a uniformly bounded type-I von Neumann
subalgebra, including every commuting normal tuple, without a coherent
matrix tower.  It also forces any negative gap certificate to stay a fixed
operator-norm distance from every finite-dimensional subalgebra, even though
its hyperfinite `2`-norm distance is zero.

That radius is not zero for every finite tuple.
`stw99-xciv-some-finite-tuple-has-positive-fd-radius` proves this from the
nonnuclearity of `R` as a C*-algebra.  The larger invariant in
`stw99-xciv-commutant-capacious-radius-controls-block-defect` replaces
finite-dimensional approximants by arbitrary subalgebras whose relative
commutant contains `I_(2,3)`.  It still bounds the block defect by twice the
operator-norm distance and includes both legs of every tensor decomposition
of `R`.  Thus a negative XCIV tuple must be uniformly far from all such
matrix or diffuse tensor cores; whether every finite tuple can nevertheless
be approximated by some commutant-capacious core remains open.
