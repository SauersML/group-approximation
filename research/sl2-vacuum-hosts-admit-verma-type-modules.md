---
rg: 2
id: sl2-vacuum-hosts-admit-verma-type-modules
kind: claim
title: A finitely presented sl_2 vacuum host that realizes every L(k) also admits a Verma-type module, so it is not simple, unless it bounds weights below by comparing two unbounded registers
distinct_from:
  sl2-casimir-cannot-separate-verma-from-finite-dimensional: that is the representation-theoretic input, that no central relation separates Verma from finite-dimensional; this is the ring-level obstruction it produces for the design target.
  capacity-chain-presentation-is-not-simple: that is the two-register capacity instance; this is the sl_2 instance of the same phenomenon, and it reduces to that regime.
  single-register-rings-divide-unit-at-finitely-many-primes: that bounds K_0 for one-register commutative designs; this is a noncommutative design and the obstruction is non-simplicity, not K_0.
artifacts:
  - research/artifacts/gq-gq-k2-q-sl2-verma.md
---

**OPEN, with a reduction (2026-09-18, lane gq-k2-q).** The argument below is a heuristic no-go of the same
strength as the lesson of `capacity-chain-presentation-is-not-simple`: it shows the sl_2 loophole (Attempt 4 of
`fp-simple-resolvent-ring-with-divisible-unit-class`) reduces to the two-register comparison that Attempt 3
already brackets. A full proof would fix a presentation class and build the module.

## The design

An *sl_2 vacuum host* is a finitely presented ring `R` with a resolvent vacuum
(`resolvent-vacuum-rings-have-no-k0-state`) giving `Q`, whose branching is produced by `sl_2`-type generators
`e, f, h` and idempotents `p_k` projecting to a highest-weight-`k` space, so that the multiplicity at level `k` is
`dim L(k) = k+1`. The concrete model is a submodule of `⊕_k L(k) ⊗ (multiplicity)`, on which `f` is locally
nilpotent: `f^(k+1) p_k = 0`.

## The obstruction

1. **Local nilpotence of `f` is not finitely presentable.** "`f` is locally nilpotent" is
   `∀ v ∃ n : f^n v = 0`, a `Π_2` condition. A finite set of ring relations (polynomial identities, idempotent
   relations, resolvent relations) is a set of `Π_1` conditions. So a finitely presented `R` whose relations hold
   on `⊕_k L(k)` also holds on modules where `f` is not locally nilpotent.
2. **Such a module exists and is highest-weight.** By
   `sl2-casimir-cannot-separate-verma-from-finite-dimensional`, no central or resolvent relation kills the Verma
   submodule `M(-k-2) ⊆ M(k)`. The only relation that does is the growing-length singular vector `f^(k+1) v_k`,
   which is not among finitely many relations. So a highest-weight module on which `f^(k+1) v_k ≠ 0`, i.e. a
   Verma-type quotient of `M(k)` strictly larger than `L(k)`, satisfies every relation of `R`.
3. **Non-simplicity.** On that module the element `f^(k+1) p_k` is nonzero, while it is `0` in the concrete model.
   So `ker(R -> R_conc)` is a nonzero proper ideal and `R` is not simple, exactly as in
   `capacity-chain-presentation-is-not-simple`.

## The only escape, and why it is the same regime

The obstruction is avoided only if the presentation forces `f` to vanish at weight `-k` on the highest-weight-`k`
space, i.e. bounds the weight below by `-k`. Detecting "current weight `= -k`" requires comparing the running
weight register `h` to the highest-weight register `k`. That is the inequality between two unbounded registers of
`capacity-chain-presentation-is-not-simple`. So:
- the sl_2 mechanism does not evade the two-register comparison; it renames it (`h` versus highest weight);
- the finite-dimensional cut is the well-foundedness (local nilpotence) that a finite presentation cannot enforce.

## Attempts

1. **Casimir (refuted).** `sl2-casimir-cannot-separate-verma-from-finite-dimensional`.
2. **Resolvent of `h` (refuted).** Same node: excluding a weight excludes it in every module.
3. **Quantum `sl_2` at a root of unity (untested).** There `f^ℓ` is central (`ℓ` = the order), so `f^ℓ = 0` is a
   single relation. But then multiplicities are bounded by `ℓ`, not growing, so `K_0` is periodic, exactly the
   one-register verdict of `single-register-rings-divide-unit-at-finitely-many-primes`. Recorded as a dead shape,
   not landed as a separate node.
