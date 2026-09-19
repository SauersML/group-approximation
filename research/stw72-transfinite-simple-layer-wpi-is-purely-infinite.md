---
rg: 2
id: stw72-transfinite-simple-layer-wpi-is-purely-infinite
kind: claim
title: Transfinite simple-layer filtrations collapse weak pure infiniteness to pure infiniteness
distinct_from:
  stw72-finite-ideal-lattice-wpi-is-purely-infinite: that theorem extracts a finite composition series from finiteness of the entire ideal lattice; this theorem assumes one continuous transfinite simple-layer series and allows the ambient ideal lattice to be infinite and highly non-linearly ordered.
  stw72-chain-ideal-wpi-is-purely-infinite: that theorem assumes all closed ideals are linearly ordered; this theorem only linearly orders the selected filtration and permits many incomparable ideals outside it.
artifacts:
  - research/artifacts/stw72-transfinite-composition-collapse-audit-2026-08-30.md
---

Let `A` be a C-star algebra admitting a continuous transfinite composition
series indexed by an ordinal `alpha`:

```text
0=I_0 proper subset I_1 proper subset ... proper subset I_alpha=A,
```

where every `I_beta` is a closed two-sided ideal of `A`,

```text
I_lambda = closure(union_(beta<lambda) I_beta)
```

at each nonzero limit ordinal `lambda<=alpha`, and every successor quotient

```text
I_(beta+1)/I_beta
```

is simple.  If `A` is weakly purely infinite, then `A` is purely infinite.

No countability, separability, nuclearity, unitality, exactness, or bound on
the ordinal length is required.

The class is nonvacuous far beyond finite ideal lattices.  For every nonzero
ordinal `alpha`,

```text
c_0(alpha,O_infinity)
```

has the displayed series with `I_beta=c_0(beta,O_infinity)` and successor
quotients `O_infinity`.  For infinite `alpha` its ideal lattice has many
incomparable members, while the algebra is nonzero and purely infinite.
