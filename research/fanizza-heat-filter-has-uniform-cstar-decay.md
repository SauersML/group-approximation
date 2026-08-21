---
rg: 2
id: fanizza-heat-filter-has-uniform-cstar-decay
kind: claim
title: The Fanizza game Hamiltonian gives a uniform rational heat-filter sequence
distinct_from:
  group-algebra-mark-reverse-kleene-collapse: that consumes one fixed finite group-algebra mark whose matrix microstates collapse; this produces a computable sequence with uniform norm decay and isolates the remaining one-sided compressor.
  fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity: that bounds one fixed nontrivial mark by a depth-dependent scalar; this has depth-dependent group-algebra elements and therefore still needs a return identifying them with one mark.
---

Use `H_m,D_R` from
`two-copy-bcs-game-hamiltonian-dominates-fanizza-signal` and put

```text
K_m=1-H_m,
a_(m,t)=D_R K_m^t in Q[Lambda_m],       t>=0.          (FHF1)
```

If `m` is a nonmember, then in every unitary representation `pi`,

```text
||pi(a_(m,t))||
 <= sqrt(C_m/(2t+1)).                                 (FHF2)
```

If `m` is a HALT member, every `a_(m,t)` is nonzero in the full group
`C*`-algebra, hence also nonzero as a rational group-algebra expression in
the represented quotient.

## Proof of uniform decay

From `D_R<=C_m H_m`, positivity and `0<=K_m<=1` give

```text
K_m^t D_R K_m^t <= C_m K_m^t H_m K_m^t.              (FHF3)
```

Therefore

```text
||D_R K_m^t||^2
 = ||K_m^t D_R K_m^t||
 <= C_m ||H_m(1-H_m)^(2t)||.                          (FHF4)
```

For `lambda in [0,1]`, the maximum of
`lambda(1-lambda)^(2t)` occurs at `lambda=1/(2t+1)` and is at most
`1/(2t+1)`.  Functional calculus proves `(FHF2)`, uniformly in matrix
dimension and indeed uniformly over all representations.

On the HALT side choose the perfect vector from `(TCH5)`.  Then

```text
K_m^t xi=xi,
a_(m,t)xi=D_R xi !=0,                                 (FHF5)
```

so every filtered element is nonzero.

## Exact claim boundary

This is not yet a nonhyperlinear group.  The element changes with `t`.
Identifying all `a_(m,t)` with one fixed mark by unitary conjugacy would be
invalid because conjugacy preserves norm and would also kill the HALT
witness.  The missing operation is a one-sided, representation-specific
compressor: an exact properly infinite HALT model may absorb the filtration,
whereas finite matrices must expose `(FHF2)` on one fixed returned carrier.

The reduction is nevertheless stronger than a generic semantic decoder.
The payload is now the explicit rational Markov operator `K_m`; the desired
Toeplitz/Leavitt cell has only to return this one computable heat-filter
sequence rather than compile an arbitrary BCS predicate directly.
