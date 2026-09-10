---
rg: 2
id: fp-upgrades-make-non-lef-and-non-lea-cheap-proof
kind: route
title: One window argument, two target classes
target: fp-upgrades-make-non-lef-and-non-lea-cheap
requires: []
---

## Why sufficient

Let `G = <X | R>` be finitely presented, `g` a nontrivial element, and let
`S` be the finite set consisting of `X`, all subwords of all relators in `R`,
and `g`.

**LEF case.**  A local embedding of `S` into a finite group `F` is a map
`phi: S -> F` that is multiplicative wherever both factors and their product
lie in `S`, and injective on `S`.  Multiplicativity across every relator subword
makes `phi` send each relator to the identity, so the assignment `x -> phi(x)`
on `X` extends to a homomorphism `G -> F`, which agrees with `phi` on `S` and
therefore sends `g` to a nontrivial element.  As `g` was arbitrary, `G` is
residually finite.  This is Vershik--Gordon, Theorem 2.2.

**LEA case.**  Run the identical argument with `F` amenable.  The resulting
homomorphism `G -> F` is nontrivial, since it separates `g` from the identity.
If `G` is simple, a nontrivial homomorphism is injective, so `G` embeds in an
amenable group and is amenable.  Contrapositive: `fp`, simple and non-amenable
force the failure of LEA.

**The consequence stated.**  An infinite simple finitely presented group has no
nontrivial finite quotient, so it is not residually finite and hence not LEF; if
it is additionally non-amenable it is not LEA.  Burger--Mozes groups are
finitely presented, infinite, simple, contain `F_2` (so are non-amenable), and
carry CAT(0), biautomaticity, type `F_infinity`, finite cohomological dimension
and the Haagerup property, which is why they witness the entire non-LEA row.

**Why the argument does not transfer.**  Soficity provides, for each finite
window and each `epsilon`, a map into a symmetric group that is multiplicative
only up to normalized Hamming distance `epsilon`, and MF likewise up to operator
norm.  The step "phi sends each relator to the identity" fails: a relator is
sent to something within `epsilon` of the identity, which does not factor
through the presented group.  Nothing in a finite presentation bounds the
accumulated error, so the window argument has no analogue.

## Scope

The negative half is a statement about the absence of a known lever, not a proof
that no lever exists; it is recorded because it explains the observed shape of
the atlas and localises what a new argument would have to supply.
