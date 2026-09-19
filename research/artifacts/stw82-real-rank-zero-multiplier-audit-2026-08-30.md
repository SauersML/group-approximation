# Audit: real-rank-zero multiplier projections

Date: 2026-08-30

Claim: `stw82-real-rank-zero-multiplier-projections`.

## Checks

1. Real rank zero passes to both multiplier corners, and its projection-
   approximate-identity characterization does not require sigma-unitality.
   No fullness of either corner is required.

2. A product of the two projection approximate-identity nets makes all four
   Peirce corners converge.  For a finite set, one pair of projection cuts
   can therefore satisfy every left and right estimate simultaneously.

3. The two cuts are orthogonal across `p` and `1-p`, so their sum is a
   projection commuting with `p`; no nested sequence is needed.

4. Off-diagonal convergence is not assumed.  It follows from
   `||(p-e)x||^2=||(p-e)xx^*(p-e)||` and the approximate-identity
   property in `pAp`, with the symmetric argument for the other three
   Peirce corners.

5. The internal compression condition is exact: `p(e+f)=e in A`.  The
   generated local stage is the orthogonal sum `QAQ direct_sum C p(1-Q)`.

6. Uniform local approximation by subalgebras of nuclear dimension at most
   `d` gives nuclear dimension at most `d`: extend the incoming finite-
   dimensional coordinate maps by Arveson's theorem and compose the
   order-zero return maps with the inclusions.  This needs neither
   separability nor a directed or sequential exhaustion.

## Scope

The theorem does not claim real rank zero for the adjoined algebra, only
equality of nuclear dimensions.  The revised local proof removes the former
sigma-unitality restriction entirely.

Outcome: **PASS**.
