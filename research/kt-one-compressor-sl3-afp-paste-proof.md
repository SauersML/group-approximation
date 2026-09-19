---
rg: 2
id: kt-one-compressor-sl3-afp-paste-proof
kind: route
title: Amalgamate the one-compressor and external crossed products over the amenable cyclic edge
target: kt-one-compressor-and-sl3-normalizer-lifts-paste
requires:
  - kt-one-compressor-normalizer-cocycle-splits
  - kt-two-compressor-normalizer-cocycle-splits
  - amenable-edge-hnn-preserves-hyperlinearity
  - finitary-extension-ce-iff-action-lifts-to-normalizer
---

Let `pr:G->S=SL_3(Z)` be the external projection.  Its restriction to
`H_A=<Gamma,A>` has image `<A>`.  If `x in H_A cap S`, then `pr(x)=x`, so
`x in <A>`.  The reverse inclusion is immediate, and hence

```text
H_A cap S=<A>.                                         (KPP1)
```

Here `A` has infinite order: a finite-order matrix cannot satisfy the strict
compression `A N^3 proper-subset N^3`.  Thus the common subgroup is infinite
cyclic.

The action maps `H_A->Aut(R)` and `S->Aut(R)` are restrictions of the same
ambient action, so they agree on `<A>` and extend by the universal property
to `P_A=H_A*_<A>S`.  At the group von Neumann algebra level the canonical
Fourier decompositions give

```text
R rtimes P_A
 ~= (R rtimes H_A) *_(R rtimes <A>) (R rtimes S).       (KPP2)
```

The two vertex algebras are Connes embeddable by the two splitting claims.
The edge algebra is hyperfinite because it is a crossed product of the
hyperfinite factor by the amenable group `Z`.  Brown--Dykema--Jung
amenable-amalgam permanence (the input used in
`amenable-edge-hnn-preserves-hyperlinearity`) makes `(KPP2)` Connes
embeddable.  Apply `finitary-extension-ce-iff-action-lifts-to-normalizer` to
obtain `(KPA3)`, including the trace condition even though the action of
`P_A` has a kernel.  Restriction of this one homomorphism supplies compatible
splittings on both vertex groups.  The argument for `B` is identical.
