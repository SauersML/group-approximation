---
title: STW XXII asymptotically dense factor-field audit (2026-08-30)
---

## Strict extension

The finite Bratteli-cube theorem used nested full matrix stages.  The new
theorem replaces them by arbitrary unital nuclear unique-trace subalgebras
`D_n` of a UHF algebra, assuming only `dist(u,D_n)->0` for every ambient
element.  The stages need not be nested or finite dimensional.  Their GNS
closures can be proper hyperfinite `II_1` subfactors, so this is a genuine
field enlargement rather than a reformulation of the matrix case.

## Nuclear realization

The one-coordinate section algebra sits in the exact sequence

```text
0 -> direct-sum_n^c0 D_n -> B -> U -> 0.
```

All terms except the middle one are nuclear, hence so is the middle one.
Finite tensor products and central restriction quotients remain nuclear.
Central disintegration is performed before completion: every C*-fibre has
a unique trace, so `T(B_K)=Prob(K)` exactly.

## Completion and expectation checks

Fibre evaluation is onto.  At a finite coordinate one uses a spike section;
at an infinite coordinate asymptotic density supplies the convergent tail.
Kaplansky approximation at finitely many selected fibres plus a partition
of unity proves that the full bounded constrained `2`-continuous section
algebra is the uniform completion.

The trace-preserving expectation onto `D_n''` is the `L^2` orthogonal
projection.  Asymptotic norm density forces its distance from every fixed
element of the ambient factor to tend to zero.  This is the only new input
needed by the nearest-point lift across a derived subset.

## Trace-free gap check

Every exposed Cantor--Bendixson layer is discrete relative to the current
derivative.  A kernel representative is cut to vanish on the next
derivative.  Arbitrary pointwise orthogonalizers of a small spectral cut
then become continuous after multiplication by its square root.  The
fibres are finite factors, whether matrix or `II_1`, so normalized support
trace at most `1/m` gives `m` orthogonal equivalent copies.  Boundedness of
a trace kills every cut.  Finite height makes the descent terminate.

## Explicit non-matrix model

In `U=bigotimes_(j>=1)M_2`, let `D_n` use the first `n` tensor factors and
every second factor thereafter.  It contains every fixed local tensor for
all sufficiently large `n`, yet its weak closure omits an infinite tensor
tail and is a proper `II_1` subfactor with diffuse relative commutant.  The
new theorem applies, whereas the matrix-stage theorem does not.

## Scope

This proves a strictly broader positive class for Problem XXII, not the
general problem.  Finite Cantor--Bendixson height is used when the gap trace
cone is descended to an isolated fibre; no conclusion is asserted at a
limit ordinal or for factor fields lacking asymptotically identity
expectations.

The later theorem `stw22-expectation-fields-have-uniform-traces` removes
the height restriction whenever those coordinate expectations extend to a
pointwise `2`-continuous expectation field over the whole base.  The
present finite-height proof remains useful when only successor-stage
expectation convergence is available and no global moving-fibre selection
has been established.
