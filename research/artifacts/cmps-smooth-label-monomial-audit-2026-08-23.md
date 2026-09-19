# CMPS smooth-label / monomial audit

**Date:** 2026-08-23  
**Primary source:** Eric Culf, Kieran Mastel, Connor Paddock, and Taro
Spirig, *The quantum smooth label cover problem is undecidable*,
arXiv:2510.03477v3.

## Verdict

There are three distinct conclusions.

1. **The raw edge syntax is already right.**  For every edge `e=(v,w)`,
   acceptance is

   ```text
   pi_(e,v)(a)=pi_(e,w)(b).
   ```

   Therefore the accepted relation is the disjoint union of the bicliques
   `pi_(e,v)^(-1)(ell) x pi_(e,w)^(-1)(ell)`.  Assigning a distinct positive
   scalar magnitude to each `ell` realizes this relation exactly as equality
   of finite-phase projective colors.

2. **Lin's fixed `qc/q` gap can be passed to this syntax.**  This is not a
   stated CMPS theorem: the authors explicitly say after Equation (2.1) that
   they do not work with the commuting-operator value.  It is an exact hybrid
   corollary of their proofs.  Forward completeness uses only copying PVMs,
   finite tensor powers, projection-fiber sums, and a trace; all work in a
   tracial von Neumann algebra.  Reverse soundness uses finite-dimensional
   PVMs, entangled projection-game parallel repetition, weighted defect
   pullback, and finite-dimensional Naimark dilation.  Combining this with
   the fixed finite synchronous-to-BCS construction and the weighted
   Cook--Levin/subdivision maps yields, for every fixed `s>0`, a finite
   smooth-label instance with perfect synchronous commuting value and
   synchronous finite-dimensional value at most `s`.  Passing through CMPS
   Lemma 20 and Theorem 19 also makes the chosen perfect tracial model
   edge-oracularizable: the PVMs at the endpoints of every sampled edge
   commute.

3. **This is not yet a monomial matrix pair or a group.**  Local
   projective-color relations do not give the column partitions of a square
   quantum-reflection matrix and do not combine edge-dependent color maps
   into one global equation `uA=Bu`.  Harris's circulant square completion
   reintroduces a Cayley/affine-coset condition, so it cannot simply be
   composed with the local color observation.  A non-circulant or auxiliary
   completion must preserve the separated game algebra as a full corner.
   Even after that, phase-safe toric groupification remains a second open
   obligation.

## Theorem map

- CMPS Definition 3: smooth-label-cover edge predicate and quantum
  synchronous/oracularizable values.
- Theorem 9: constant-gap `3SAT5` clause-variable source in the
  finite-dimensional quantum model.
- Lemma 12 and Corollary 13: `(J,R)` dummy projection game and quantum
  soundness amplification.  The displayed perfect tensor-product strategy
  extends verbatim to a finite tensor power of a tracial von Neumann algebra.
- Theorem 10: reduction from the dummy game to smooth label cover.  Equations
  (3.2)--(3.3) expose the forward tracial construction and reverse
  finite-dimensional soundness construction.
- Corollary 18 and Theorem 19: finite-dimensional oracularizable completeness
  after the stronger Lemma 20 source.  The displayed completeness argument
  uses only products of commuting source observables, so it also transports
  the chosen perfect tracial source model.  The statements still do not
  assert a commuting-operator soundness theorem.
- Lemma 20: radius-two incidence commutation on a chosen finite-dimensional
  completeness strategy.  It is useful for oracularization, but it neither
  makes the nonaffine label domains affine nor supplies a monomial square
  completion.
- Lemmas 31--32 and Theorem 33: weighted finite-dimensional defect pullback
  through fixed-degree replacement.  Exact forward completeness is the
  evident copying map used by the construction and is model-independent.

## Precise model boundary

The useful separated output is

```text
omega_co^s(S)=1,             omega_q^s(S)<=s,
[P_v^a,P_w^b]=0 on every edge in the chosen trace.
```

This rules out a perfect `qa`/`R^omega` model for the synchronous game
algebra.  No claim is made that CMPS prove a commuting-operator soundness gap;
they do not need one, and Lin's input has commuting value one.  Likewise, no
claim is made that Theorem 19's finite-dimensional oracularizable strategy is
the desired non-CE strategy.

## Cairn wiring

- `smooth-label-cover-edges-are-finite-phase-projective-color`: established
  local syntax.
- `lin-gap-smooth-label-cover-projective-color-game`: established hybrid
  `qc/q` lowering.
- `smooth-label-cover-gap-full-corner-monomial-realization`: open global
  square/full-corner compiler.
- `lin-smooth-label-monomial-phase-safe-route`: alternative route to the
  existing phase-safe toric target, with full-corner realization and
  phase-safe groupification kept as separate gates.
