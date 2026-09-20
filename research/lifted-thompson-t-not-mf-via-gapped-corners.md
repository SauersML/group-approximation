---
rg: 2
id: lifted-thompson-t-not-mf-via-gapped-corners
kind: route
title: A tracial conjunct (the shadow residual of T-bar is full) and a norm-only conjunct (gapped commutant corners of the centre) together kill z in every corona representation
target: lifted-thompson-t-is-not-mf
requires:
  - lifted-thompson-t-shadow-residual-is-full
  - lifted-thompson-t-centre-has-gapped-commutant-corners
  - lifted-thompson-t-shadow-residual-dichotomy
---

Notation as in `lifted-thompson-t-shadow-residual-dichotomy`.  Write (A)
for `lifted-thompson-t-shadow-residual-is-full`, that is `S(T̄) = T̄`, and
(EC′) for `lifted-thompson-t-centre-has-gapped-commutant-corners`.

## Proof

Let `rho : T̄ -> U(Q)` be a corona homomorphism.  We show `rho(z) = 1`.

- Suppose `rho(z) != 1`.  By (EC′), `rho` has a gapped commutant corner.
- By item 2(b) of the dichotomy, this gives `S(T̄) = 1`.
- `T̄` is nontrivial, so `S(T̄) = 1` contradicts (A).

Hence `rho(z) = 1` for every `rho`, which is `lifted-thompson-t-is-not-mf`. ∎

The case `rho(z) = 1` needs nothing.  But note that, by item 3 of the
dichotomy, (A) also makes every such `rho` trivial: it factors through `T`,
and `T` is not MF.

## The decomposition is exact

Both conjuncts follow from the target.
- Target implies (A): item 4 of the dichotomy.
- Target implies (EC′) vacuously: every `rho` has `rho(z) = 1`.

So

```text
lifted-thompson-t-is-not-mf  <=>  (A) AND (EC′).
```

Compare `lifted-thompson-t-not-mf-via-central-eigencorners`, which is
`thompson-t-has-full-mf-radical AND lifted-thompson-t-centre-has-commutant-eigencorners`.
- (A) is stronger than full radical of `T` (item 3 of the dichotomy).
- (EC′) is weaker than the eigencorner conjunct, and it asks only for
  invertibility, not for a scalar corner.
- (A) is purely tracial.  (EC′) is purely norm-theoretic, and it is refuted
  for general groups by `o2-suspension-central-unitary-evades-commutant-corners`.

## Kazhdan hygiene

No Property `(T)`, Kazhdan projection or Kazhdan transport is used.
