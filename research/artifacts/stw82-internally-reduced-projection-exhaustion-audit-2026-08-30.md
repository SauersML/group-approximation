# Audit: internally reduced multiplier-projection exhaustions

Date: 2026-08-30

Claim: `stw82-internally-reduced-projection-exhaustions`.

## Exact stage checks

1. Strict convergence of the increasing multiplier projections implies
   `Q_naQ_n->a` in norm for every `a in A`; no norm convergence of `Q_n`
   is asserted.

2. Exact commutation makes `pQ_n` and `p(1-Q_n)` orthogonal projections.
   The separate internality hypothesis `pQ_n in A` is essential when
   `Q_n` lies only in `M(A)`.  Support by `Q_n` then places `pQ_n` in the
   hereditary algebra `Q_nAQ_n`.

3. The tail annihilates that hereditary algebra on both sides.  Thus the
   finite stage is an actual orthogonal direct sum with one scalar
   projection, not merely a split extension and not a quasidiagonal
   approximation.

4. For nonconstant block increments, nestedness follows from the exact
   identity

   ```text
   p(1-Q_n)=p(1-Q_(n+1))+p(Q_(n+1)-Q_n).
   ```

   The increment is internal because it is the difference of the two
   assumed internal compressions, and it is supported by `Q_(n+1)`.

5. For nonzero `A`, hereditary permanence bounds every nonzero compressed
   stage by `dim_nuc(A)`, while a possibly zero compressed stage plus `C`
   has dimension zero.  Thus direct sums with `C` do not add a colour;
   inductive-limit permanence gives the upper bound and ideal permanence
   gives equality.  The zero-algebra case is vacuous because `M(0)=0`.

## Module examples and scope

6. A bounded orthogonal family of finite-block projections has a strict
   sum in `M(B tensor K)`.  Cumulative block projections reduce that sum
   and its compressions lie in the finite matrix corners when `B` is
   unital.

7. Block sizes and projection classes may vary arbitrarily.  For `B=C`,
   the alternating diagonal projection has both infinite rank and infinite
   corank, so no unitary can carry it to either available constant
   coefficient projection `0` or `1`.

8. The theorem does not assert that an arbitrary multiplier projection
   admits such an exact reducing exhaustion.  It is independent of
   quasicentral overlap cuts: the `Q_n` need not asymptotically commute with
   elements of `A` in norm.

Outcome: **PASS**.
