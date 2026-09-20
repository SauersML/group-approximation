---
rg: 2
id: lifted-thompson-t-centre-has-gapped-commutant-corners
kind: claim
title: "Every corona representation of T-bar that moves the central translation z has a nonzero commutant corner on which rho(z) - 1 is invertible"
distinct_from:
  lifted-thompson-t-centre-has-commutant-eigencorners: that asks for an exact scalar eigencorner rho(z) P = lambda P with lambda != 1; this asks only that rho(z) P - P be invertible in PQP. Exact eigencorners are gapped, so that claim implies this one, and one approximate corner with error below |lambda - 1| already suffices here.
  o2-suspension-central-unitary-evades-commutant-corners: that exhibits, for a general group, a corona map whose central unitary has no gapped commutant corner at all; so the analogue of this claim is false for general groups with centre, and any proof must use T-bar.
  commutant-projection-extraction: that is the refuted general extraction principle; this is the T-bar-specific, invertibility-only instance.
---

**OPEN.**  Notation as in `lifted-thompson-t-shadow-residual-dichotomy`.
Claim (EC′): for every corona homomorphism `rho : T̄ -> U(Q)` with
`rho(z) != 1`, there is a nonzero projection `P in rho(T̄)' ∩ Q` such that

```text
rho(z) P - P   is invertible in   P Q P.
```

## Sufficient forms

Each of the following implies (EC′) for a given `rho`:
- an exact eigencorner `rho(z) P = lambda P` with `lambda != 1`;
- an approximate one: a nonzero commutant projection `q` and some `lambda`
  with `||(rho(z) - lambda) q|| < |lambda - 1|` (item 2(c) of the
  dichotomy);
- `sp(rho(z) P)` not connected, or not containing `1`, for some nonzero
  commutant projection `P`.  Cut to a clopen piece missing `1`.

## What it is worth

- With `lifted-thompson-t-shadow-residual-is-full` it gives
  `lifted-thompson-t-is-not-mf`.  This is the route
  `lifted-thompson-t-not-mf-via-gapped-corners`.
- Under that tracial conjunct (A), a gapped corner cannot exist (item 2(b)).
  So under (A), (EC′) says exactly that no `rho` moves `z`.  The conjunct
  is where all the norm content of the flagship hole sits.
- Its only obstruction on record is the O2-suspension configuration: a
  central unitary with connected full-circle spectrum in every commutant
  corner.  By item 3 of the dichotomy, a counterexample to the target under
  (A) must look exactly like this.

## How it could fail

A single corona homomorphism of `T̄` that moves `z` while every nonzero
commutant corner has `sp(rho(z) P)` a connected arc through `1` refutes
(EC′).  It would need neither (A) nor its negation.
