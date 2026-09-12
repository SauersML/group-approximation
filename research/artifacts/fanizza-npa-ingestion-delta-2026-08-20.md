# Fanizza et al. NPA paper: Cairn ingestion delta (2026-08-20)

The user supplied the complete manuscript of Fanizza--Kroell--Mehta--
Paddock--Rochette--Slofstra--Zhao, *The NPA hierarchy does not always attain
the commuting operator value* (arXiv:2510.04943v4), with the instruction to
wire useful material into Cairn without duplication.

## Already represented; not re-imported

- the computable `L`-family and distinguished signal estimate:
  `fanizza-et-al-computable-bcs-signal-family` and
  `fanizza-turing-bcs-signal-collapse`;
- the polynomial-cost projection-doubling tape:
  `fanizza-bcs-polynomial-doubling-tape`;
- the fixed nonlinear predicate menu after flattening:
  `fanizza-final-bcs-has-fixed-nonlinear-menu`;
- the self-referential nonzero BCS signal and the open matrix-only
  groupification problem:
  `self-referential-bcs-nonzero-signal-collapse` and
  `hs-groupify-self-referential-bcs-signal`.

## New interfaces imported

1. `nested-conjugacy-bcs-embedding-has-quadratic-depth-loss` records the
   general trace-preserving embedding and exact
   `2^16 M^2 ell^2 Lambda` certificate loss, rather than only its use inside
   the Fanizza machine.
2. `near-perfect-bcs-strategy-gives-synchronous-relator-state` records the
   explicit `4^(M+2)kM^3` game-loss-to-relator/synchrony modulus.
3. `fanizza-self-referential-game-never-attains-npa-limit` records the
   recursion-theorem game with equality at the limit and strict separation at
   every finite NPA level.  This is distinct from Cairn's existing MIPco
   fixed point, whose conclusion is a commuting-versus-finite-dimensional
   value gap.

## Boundary relevant to the main goal

The paper now closes two upstream interfaces needed by Cairn: arbitrary
nested-conjugacy algebra relations can be compiled into an ordinary finite
BCS with controlled polynomial loss, and near-perfect BCS strategies produce
exactly the synchronous approximate states used by the MSZ weighted
doubling argument.  Neither theorem converts the remaining additive
projection relation into group words or supplies a matrix-only marked-word
decoder.  That boundary is now stated explicitly in
`hs-groupify-self-referential-bcs-signal`.
