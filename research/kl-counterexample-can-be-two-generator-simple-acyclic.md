---
rg: 2
id: kl-counterexample-can-be-two-generator-simple-acyclic
kind: claim
title: Any Kervaire--Laudenbach counterexample can be taken two-generator, simple and integrally acyclic
distinct_from:
  kl-counterexample-can-be-two-generator-simple: that is the Schupp envelope, simple with uncontrolled homology; this adds integral acyclicity through the Palmer--Wu envelope, so the coefficient group has trivial Schur multiplier and trivial centre at once.
  kl-counterexample-can-be-superperfect-quasisimple: that asks only for H_1 = H_2 = 0 with G/Z(G) simple and is derived from this node; this is the stronger simple acyclic statement.
  kl-counterexample-absorbs-any-countable-group: that puts a prescribed countable group inside a simple counterexample; this does the same inside a simple acyclic counterexample.
  kl-counterexample-can-be-finitely-presented-simple: that asks for finite presentation together with simplicity and needs Boone--Higman; this gives simplicity with acyclicity and two generators, without finite presentation.
artifacts:
  - research/artifacts/hl-kl-minimal-counterexample-2026-09-14.md
---

If `kervaire-laudenbach-nonsingular-conjecture` fails at degree `m`, then it
fails at degree `m` over an infinite two-generated simple group `S` with
`H_n(S; Z) = 0` for every `n >= 1`. Moreover:
- `S` may be chosen to contain a copy of any prescribed countable group;
- for such a failure, `(S * <t>)/<<w>> = C_|m|`.

In particular `S` is a two-generator superperfect quasisimple counterexample
with trivial centre. That settles
`kl-counterexample-can-be-superperfect-quasisimple`.

## What it changes

**Degree-two invariants of the coefficient group are blind.**
- A counterexample of this shape kills its whole coefficient group while
  `H_1 = H_2 = 0`.
- So no argument that watches only the homology of the coefficient group can
  exclude counterexamples.
- `kl-failure-yields-a-schur-kill` is consistent with this. Its torus amalgam
  is a different, non-acyclic coefficient group.

**The classical form is a contractible complex.** At `m = ±1`, the complex
`K(S,1) ∨ S^1 ∪_w e^2` is contractible (artifact §5). So the classical
conjecture fails iff some complex of that shape, with nontrivial `S`, is
contractible.

## What it does not change

- **Finite presentation.** The envelope is the twisted Brin--Thompson group of
  the regular action, which is not known to be finitely presented.
  - The finitely presented acyclic normal form is
    `kl-counterexample-can-be-finitely-presented-acyclic`.
  - Finite presentation together with simplicity is still
    `kl-counterexample-can-be-finitely-presented-simple`.
- **Non-hyperlinearity.** As a normal form for non-hyperlinear groups this is
  no news: Palmer--Wu embed every finitely generated group into such
  envelopes.

DERIVATION
kl-simple-acyclic-envelope-proof
