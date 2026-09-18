---
rg: 2
id: finite-double-coset-space-with-free-minimal-coset-sft
kind: claim
title: Some finitely presented group Λ and finitely generated Δ ≤ Λ with Δ\Λ/Δ finite carry a coset SFT on Λ/Δ on which Λ acts freely and minimally
distinct_from:
  cornulier-regime-coset-sfts-are-quantum-rigid: that proves every coset shift over a finite double-coset space is quantum rigid; this asks for a free minimal one, which would then be rigid for free.
  set-transitive-coset-shifts-have-only-constant-minimal-sets: that rules the question out whenever the action has (IS); this asks for a finite double-coset space without (IS) where it succeeds.
  two-sided-free-group-coset-sfts-collapse-under-cyclic-descent: that shows the descent-regime version over F_2 x F_2 collapses to finite subshifts; this is the determinism-free version, over a finite double-coset space.
---

**OPEN.** The Cornulier-regime shortcut to gate G2 of `research/artifacts/gq-bh-synthesis-master-route.md`.

## Statement

There are a finitely presented group `Λ`, a finitely generated subgroup `Δ` with finitely many double
cosets, a finite alphabet `A`, and a nonempty closed Λ-invariant `Z ⊆ A^(Λ/Δ)` with the following
properties:
- `Z` is cut out by finitely many forbidden patterns on Λ-balls;
- `Λ` acts on `Z` freely and minimally.

## Consequence

By `cornulier-regime-coset-sfts-are-quantum-rigid`, the coset SFT `X_Z` would be a quantum rigid free
minimal SFT over `Λ`, and `LC(X_Z, k) ⋊ Λ` would be finitely presented and central simple.

## Constraints

- **(IS) must fail** (`set-transitive-coset-shifts-have-only-constant-minimal-sets`). That excludes
  highly transitive and order-transitive actions, including `V`, `F`, `T` and `CT_P(Z)` on their
  standard sets.
- **One end.** `Λ` must be one-ended. A nonempty free SFT is strongly aperiodic, and finitely presented
  groups with such SFTs are one-ended (Cohen, context only).
- **Solvable word problem.** `Λ` must have solvable word problem (Jeandel, context only).
- **An avoidable pair relation.** Some Λ-invariant relation on pairs must be avoided by an infinite set.
  So the natural candidates are actions with finitely many orbitals that preserve a nontrivial graph,
  such as bounded-diameter, locally infinite orbital graphs.
- **Canonization (heuristic, not proved).** For oligomorphic closures, Ramsey canonization seems to put
  points with nontrivial stabilizer into orbit closures (see the `V × V` remark in the (IS) node). So a
  witness probably needs finitely many orbits on pairs but infinitely many on triples.
