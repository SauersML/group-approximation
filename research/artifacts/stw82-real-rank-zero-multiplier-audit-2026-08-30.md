# Audit: real-rank-zero multiplier projections

Date: 2026-08-30

Claim: `stw82-real-rank-zero-multiplier-projections`.

## Checks

1. Compression of a countable approximate unit of `A` makes both multiplier
   corners sigma-unital.  No fullness of either corner is required.

2. Real rank zero passes to hereditary subalgebras.  Sigma-unitality upgrades
   the projection approximate-unit characterization to increasing sequences
   in both diagonal corners.

3. The corner projection sequences are orthogonal across `p` and `1-p`, so
   their termwise sums are increasing projections commuting with `p`.

4. Strict convergence on off-diagonal corners is not assumed.  It follows
   from `||(p-e_n)x||^2=||(p-e_n)xx^*(p-e_n)||` and the approximate-unit
   property in `pAp`, with the symmetric argument for the other three
   Peirce corners.

5. The internal compression condition is exact: `p(e_n+f_n)=e_n in A`.
   The reducing-exhaustion theorem therefore applies directly.

## Scope

Sigma-unitality is used to obtain sequential increasing projection
approximate units.  The theorem does not claim real rank zero for the
adjoined algebra, only equality of nuclear dimensions.

Outcome: **PASS**.
