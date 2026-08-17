---
rg: 2
id: leavitt-evaluation-splits-as-module-map
kind: claim
title: The Leavitt evaluation map splits as a module map
distinct_from:
  binary-leavitt-family-lifts-into-unit-corner: that asks for a unital *ring* section of the corner evaluation, which carries the multiplicative Leavitt relations; this asks only for a left-module section of the whole-algebra evaluation, which need not respect multiplication and is not touched by the augmentation no-go that forces that node into a corner
  leavitt-corner-kernel-is-jacobson-radical: that is the other structural sufficient condition in the graph, a hypothesis about the corner's radical that makes a quotient argument legal without exhibiting anything; this is a hypothesis about a complement, and produces elements outright
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the element-level target this claim manufactures; this is the structural statement, strictly stronger and provable by different means
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Prove that the evaluation map

    pi : A = F_2[G] ->> R = L_(F_2)(1,2),       G = R^x,

splits as a map of **left `A`-modules**: some `A`-linear `sigma : R -> A`
with `pi . sigma = id_R`.  Equivalently `R` is projective as a left
`A`-module, or `ker(pi)` is a direct summand of `A`.

By `leavitt-direct-finiteness-failure-from-module-splitting` this produces
`b a = 1 != a b` in `A` outright, hence refutes Kaplansky direct finiteness
and, through the surjunctivity lane, Gottschalk's conjecture.

## The idempotent form, which is where the corner lane meets this one

`R` is cyclic over `A`, so a splitting is the same as an idempotent
description of the kernel.  If `sigma` exists, put `e = sigma(1_R)`; then
`A`-linearity gives `sigma(pi(s)) = s e`, so `sigma(R) = A e`, `e^2 = e`,
`pi(e) = 1_R` and `ker(pi) = A(1 - e)`.  Conversely any idempotent `e` with

    pi(e) = 1_R      and      A e n ker(pi) = 0

splits `pi`.  So the claim is: *some* idempotent lying over `1_R` has left
ideal meeting the kernel trivially.

This is a concrete question, because the graph already owns an idempotent
lying over `1_R`: `e = [g] + [g^2]` for the order-three unit `g` of
`leavitt-corner-idempotent-unital-surjection`, which has `pi(e) = 1_R`
exactly.  Whether `A e n ker(pi) = 0` for that `e` is unexamined here.  A
negative answer for it says nothing about other idempotents; a positive answer
closes this claim.

## Why "module" and not "ring"

A ring section is impossible: it would place a full binary Leavitt family
inside `F_2[G]`, which the augmentation forbids — the scalar half of
`augmentation-blocks-leavitt-family-proof` needs only a unital map to a
domain, and this is exactly why `binary-leavitt-family-lifts-into-unit-corner`
has to be posed in a corner of augmentation zero.  The entire content of this
claim is the distance between *direct summand* and *subring*.

## Dynamical reading

Dualizing `A = sigma(R) (+) ker(pi)` gives an equivariant linear complement to
the proper subshift `X = ker(pi)^perp` inside the full shift.  That complement
is what is missing when one tries to extend the strict self-embedding of `X`
to the full shift; that no such extension comes for free is
`subshift-self-embedding-carries-no-surjunctivity-content`.

No evidence for or against is known here.  It is recorded because it is a
clean structural sufficient condition that lives in the whole algebra rather
than in a corner, not because it is believed.
