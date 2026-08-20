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

By `(TFS4)`, every active selector sector has `m` copies of its unique
`2D`-dimensional `B_f` simple, while every inactive sector has `m` copies of
each of its two `D`-dimensional simples. Therefore

```text
dim End_(B_f)(H)=(K_1+2K_0)m^2=(L-K_1)m^2.       (SFR2)
```

Restriction to the corrected child has one `D`-dimensional simple for each
pair `(x,+/-)`. The active `B_f` simple restricts to both corrected child
branches, and the two inactive simples restrict to one branch each. Hence
every one of the `L` child simples has multiplicity `m`, so

```text
dim End_(C_f)(H)=L m^2.                            (SFR3)
```

Since `C_f<=B_f`, the two Reynolds projections are nested orthogonal
projections and

```text
rank(E_C-E_B)=dim End_(C_f)(H)-dim End_(B_f)(H)=K_1m^2.
```

There are `2^k` selector sectors, each of Hilbert dimension `2Dm`; therefore
`d=2^k(2Dm)=LDm`. Division by `d^2` proves `(SFR1)`.

For the approximate statement, exactify the fixed finite group `Rhat_f` and
average its exact conjugation table. A finite average is Lipschitz in its
finitely many unitary entries, while the finite-group correction theorem
bounds those entrywise changes by the fixed correction modulus. This yields
the asserted `O(sqrt(E))` comparison without any dependence on `d`.
