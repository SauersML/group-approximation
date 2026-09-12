---
rg: 2
id: stw62-kk-uniqueness-szabo-proof
kind: route
title: Apply Szabo's K1-injectivity theorem for Paschke dual algebras
target: stw99-problem-lxii-kk-uniqueness
requires: []
artifacts:
  - research/artifacts/stw62-kk-uniqueness-literature-import-2026-08-30.md
---

This is the trivial-group specialization of Gabor Szabo,
[*The uniqueness theorem for Kasparov
theory*](https://arxiv.org/abs/2601.23029), Theorem 4.6.  Its hypotheses become
exactly a separable domain `A`, a sigma-unital stable codomain `B`, and an
absorbing Cuntz pair `phi,psi:A->M(B)`.  The theorem says that the pair's
class is zero in `KK(A,B)` if and only if the two representations are
strongly asymptotically unitarily equivalent.

For the non-equivariant proof mechanism, Szabo's Corollary 2.9 makes the
Paschke relative commutant

```text
Q(B) intersect bar(phi)(A)'
```

`K_1`-injective.  Absorption supplies an asymptotic unitary conjugacy in
`M(B)`.  Under Paschke duality, `[phi,psi]=0` says that the initial
implementing unitary has zero `K_1` class in this relative commutant.
`K_1`-injectivity makes it homotopic to the identity.  Concatenating that
homotopy with the absorbing path gives a norm-continuous path in `U(1+B)`
starting at `1` and asymptotically conjugating `phi` to `psi`.  Strong
asymptotic unitary equivalence implies equality of the corresponding
`KK`-classes, proving the reverse implication as well.

Schafhauser--Tikuisis--White, Addendum 17.1 to
[*Nuclear C-star algebras: 99
problems*](https://arxiv.org/abs/2506.10902v2), explicitly identifies this
paper as the positive solution of Problem LXII and notes that the proof does
not settle the unrestricted `K_1`-injectivity Problem LXI.
