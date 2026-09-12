---
rg: 2
id: symmetrized-full-reset-forces-fixed-reynolds-density-proof
kind: route
title: Subtract the exact Wedderburn commutant dimensions on the reset ray
target: symmetrized-full-reset-forces-fixed-reynolds-density
requires:
  - translation-symmetrized-full-schur-reset
  - symmetrized-reset-collapses-schur-flow-to-one-ray
---

By `(TFS5)`, every active selector sector has `2n` copies of its unique
`2D`-dimensional `B_f` simple, while every inactive sector has `n` copies of
each of its four `D`-dimensional simples. Therefore

```text
dim End_(B_f)(H)=K_1(2n)^2+4K_0n^2=2L n^2.       (SFR2)
```

Restriction to the corrected child has one `D`-dimensional simple for each
pair `(x,+/-)`. The active `B_f` simple restricts to both corrected child
branches. Of the four inactive simples, two restrict to each corrected child
branch. Hence every one of the `L` child simples has multiplicity `2n`, so

```text
dim End_(C_f)(H)=L(2n)^2=4L n^2.                  (SFR3)
```

Since `C_f<=B_f`, the two Reynolds projections are nested orthogonal
projections and

```text
rank(E_C-E_B)=dim End_(C_f)(H)-dim End_(B_f)(H)=2Ln^2.
```

There are `2^k` selector sectors, each of Hilbert dimension `4Dn`; therefore
`d=2^k(4Dn)=2LDn`. Division by `d^2` proves `(SFR1)`.

The contribution to `(SFR2)` and `(SFR3)` is the same in every selector
sector. This verifies directly that the wall density is not the nonlinear
predicate signal; that signal is the linear surplus count in `(SRC7)`.

For the approximate statement, exactify the fixed finite group `Rhat_f` and
average its exact conjugation table. A finite average is Lipschitz in its
finitely many unitary entries, while the finite-group correction theorem
bounds those entrywise changes by the fixed correction modulus. This yields
the asserted `O(sqrt(E))` comparison without any dependence on `d`.
