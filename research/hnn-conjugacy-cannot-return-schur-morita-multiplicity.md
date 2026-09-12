---
rg: 2
id: hnn-conjugacy-cannot-return-schur-morita-multiplicity
kind: claim
title: Plain HNN conjugacy cannot return a Schur restriction multiplicity as the next packet input
distinct_from:
  schur-rank-output-is-not-a-scalar-selector: that rules out reading the rank bit as a scalar selector; this rules out reading its doubled module multiplicity through ordinary stable-letter conjugacy.
  termwise-finite-reynolds-holonomy-has-zero-rank-gap: that treats adjoint Reynolds tables; this is the direct representation-module obstruction for the Schur inclusion itself.
---

Let `A_f<=B_f` be an active Schur packet sector, with unique baseline simple
`S` and full-packet simple `T` satisfying

```text
T downarrow_(A_f)=S directSum S.                              (HCM1)
```

An ordinary HNN edge or amalgamating stable letter can identify only
isomorphic subgroup representations. In every finite-dimensional unitary
representation, such a relation gives a unitary equivalence and therefore
preserves the complete weighted multiplicity vector. It cannot turn the two
copies on the right of `(HCM1)` into one copy of the next `B_f` input.

Consequently a sequential Schur compiler cannot realize its module-return
edge by relations of the form

```text
s h s^(-1)=phi(h)
```

alone. The return must contain a genuinely non-Bass--Serre operation: a
proper corner/compressor, a projective automorphism cocycle, an adjoint
Reynolds comparison not induced by termwise conjugacy, or another
finite-dimensional-only Morita mechanism.
