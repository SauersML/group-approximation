---
rg: 2
id: coherent-summable-gap-clifford-tower
kind: claim
title: Compile amplified quantum gap into a coherent summable-loss Clifford tower
distinct_from:
  hs-schur-packet-gap-amplification: that asks for a one-step doubling inequality at bounded packet scale; this permits a whole self-similar tower but demands jointly reducing carriers whose total loss is summable.
  same-model-supercritical-clifford-trigger: that detects the current dimension and asks for one larger finite Clifford challenge; this uses no dimension oracle and instead places every finite Clifford rank on one positive common carrier.
  toeplitz-tail-retains-contextual-schur-density: that asks for a survive-or-recurse conditional-expectation dichotomy for one local Schur wall; this states the alternative terminal invariant that such recursion may construct.
---

OPEN.  Starting from `oracularizable-tracial-nonru-game-exists`, choose a
sequence of finite projection-game amplifications with finite-dimensional
values `epsilon_N` satisfying

```text
sum_N epsilon_N < 1.                                        (CSG1)
```

Perfect commuting/oracularizable play tensorizes, so completeness remains
exact.  Groupify the amplified losing event at level `N` by a bounded-scale
Schur--Clifford composition and a fixed self-similar return so that every
sufficiently accurate finite matrix model supplies a central (or jointly
reducing) projection `C_N` with

```text
tau(1-C_N) <= epsilon_N + K p(N) sqrt(E),                    (CSG2)
```

and the first `N` returned relative Pauli cells satisfy `(SRC2)` on `C_N`.
The relator contribution must enter through a geometrically weighted or
first-hit summable ledger, so that

```text
sum_N tau(1-C_N)<1                                          (CSG3)
```

whenever the marked word remains separated and `E` is below one fixed
constant.

Then `summable-reducing-carriers-force-infinite-clifford-capacity` contradicts
finite dimensionality.  Unlike a hyperlinear-profile lower bound, the tower
lives in the same candidate matrix model and simultaneously asks for every
finite Clifford rank on one nonzero reducing corner.

The source and terminal arguments are already available:

1. `oracularizable-tracial-nonru-game-exists` supplies exact tracial
   completeness and a finite-dimensional gap;
2. projection-game repetition makes the finite-dimensional winning values
   summable;
3. the Schur compiler turns Boolean loss into one relative Pauli cell;
4. `summable-reducing-carriers-force-infinite-clifford-capacity` is the exact
   finite-matrix contradiction.

The missing theorem is the middle **coherence** statement.  Levelwise packet
exactification only gives unrelated large projections and is insufficient.
The Toeplitz head/deep-tail factorization is the candidate mechanism: the
level-`N` head acts on a matrix factor while `sigma^N(T)` acts on its external
multiplicity, so a successful recursion must place the later carriers in that
same reducing multiplicity algebra.  This is precisely where the packet head
actuator and Fanizza first-hit accounting should be combined.

## Falsification fences

- If `(CSG2)` holds for arbitrary classically inconsistent CSPs without using
  the quantum finite-dimensional gap, the construction has accidentally
  globalized the selectors.
- If the carrier merely has large trace but does not reduce the earlier cells,
  the common-carrier conclusion is false.
- If the constants grow with the amplification level before geometric
  weighting, the result is only a hyperlinear-profile bound.
- An exact trace-functorial version is impossible by
  `regular-trace-blocks-exact-local-predicate-return`; the proof must use
  finite packet multiplicity or matrix rank.

## Attempts

- **Intersect arbitrary large level carriers:** invalid. Their ranges need
  not reduce the earlier Pauli cells, so a word from one cell can move the
  intersection outside another carrier. The terminal divisibility argument
  needs a common reducing corner, not merely positive set-theoretic overlap.
- **Use the Toeplitz head/deep-tail factorization:** active. Later carriers
  should live in the residual tail multiplicity algebra, which automatically
  commutes with and reduces the earlier finite heads. The missing estimate is
  summable control of mass lost when passing from one tail carrier to the
  next; polynomial local word costs must be paired with geometric first-hit
  weights.
- **Twisted Nekrashevych alternative:**
  `nekrashevych-clifford-sign-tape` supplies internal subtree transport and
  relative CAR cells if its self-similar central cocycle exists. The sign twist
  is mandatory: `untwisted-sign-replication-flips-minus` rules out copying a
  negative sign by the plain product of child signs. Quantitative coherence is
  then a still-missing sibling trace-independence certificate.
