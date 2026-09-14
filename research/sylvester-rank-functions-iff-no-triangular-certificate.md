---
rg: 2
id: sylvester-rank-functions-iff-no-triangular-certificate
kind: claim
title: A ring has a Sylvester matrix rank function exactly when no identity matrix dominates a larger one through minors and triangular moves
distinct_from:
  twisted-leavitt-corner-fullness-equals-absence-of-k0-states: that shows, on twisted Leavitt-visible factors, that K_0 states exist iff the rank condition holds, a minors-only certificate; this characterizes Sylvester matrix rank functions on any ring by certificates that also allow triangular moves.
  simple-group-rank-functions-are-augmentation-or-detecting: that classifies the Sylvester rank functions a simple group algebra can carry; this decides, for any ring, whether one exists at all.
artifacts:
  - research/artifacts/state-upgrade-kill-test-2026-09-12.md
---

**ESTABLISHED.** Let `A` be a unital ring. Let `<~` be the minor order on rectangular matrices
(`M <~ N` iff `M = X N Y`), and `<=_T` the smallest relation that contains `<~`, contains
`A (+) B <=_T [[A, C], [0, B]]`, and is transitive and compatible with block sums.

1. `A` carries a Sylvester matrix rank function iff there is no `q >= 0` with `I_(q+1) <=_T I_q`.
   Such a relation is witnessed by a finite chain of minor steps and triangular steps.
2. `A` carries a matrix state (additive, `<~`-monotone, 1 at `I_1`) iff there is no `q` with
   `I_(q+1) <~ I_q`, that is, iff `A` has the rank condition, iff `(K_0(A), [A])` admits a state.

So a ring with the rank condition carries a Sylvester rank function iff every triangular identity
certificate over it flattens to a minor certificate. That flattening is the whole content of step (U1)
of `ternary-anti-central-states-force-nontrivial-rank-models`.

Both properties are local: they hold for `A` iff they hold for every finitely generated subring.

Proof: Theorems 2.1–2.2 of the artifact. Goodearl–Handelman (census Theorem A(b)) is applied to the
Grothendieck group of matrices modulo mutual domination, and then the unit is absorbed.
