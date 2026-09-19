# Audit: projectional cuts on the multiplier overlap

Date: 2026-08-30

Claim: `stw82-projectional-overlap-cuts-preserve-dimension`.

## Checks

1. `I=L intersect R` is an ideal of `A`, and every multiplier of `A`
   preserves it.  Hence it remains an ideal after adjoining `p`.

2. Quasicentrality is checked on both generators of `K=A+C p`: all of `A`
   and the single multiplier projection `p`.  Density then gives
   quasicentrality in `K`.

3. An approximate unit of projections quasicentral in the middle algebra is
   exactly the quasidiagonality input used by the nuclear-dimension maximum
   theorem for separable extensions.

4. The quotient is not estimated by the generic extension bound.  Its exact
   decomposition as `(A/L) direct_sum (A/R)~` makes its nuclear dimension at
   most `dim_nuc(A)` by quotient and unitization permanence.

5. The other endpoint is the ideal `I` of `A`, so its dimension is also at
   most `dim_nuc(A)`.  Ideal monotonicity supplies the reverse inequality
   after applying the quasidiagonal maximum theorem.

6. In the strict example, the diagonal representation of `C_0((0,1])` is
   faithful and has zero intersection with the compacts because every open
   set is visited infinitely often.  Initial-coordinate projections commute
   with the diagonal image and approximate the compact overlap.

7. Both one-sided supports surject onto `C_0((0,1])`.  Since this algebra
   has no nonzero projections, neither support can have a projectional
   approximate unit.  Thus the example is not covered by the previous
   one-sided hypothesis.

8. The common compact matrix ideal is essential, making both larger proper
   supports essential and therefore noncomplemented.  The two quotient
   computations and quasidiagonal maximum theorem give nuclear dimension
   one exactly.

## Scope

The hypothesis is relative and may be strictly smaller than projectional
control of a one-sided support, but it still forces the overlap extension to
be quasidiagonal.  It does not resolve a genuinely nonquasidiagonal overlap
extension.  Finite-spectrum positive cuts alone do not imply the required
projectional cuts.

Outcome: **PASS**.
