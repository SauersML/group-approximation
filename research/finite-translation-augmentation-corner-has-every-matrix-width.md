---
rg: 2
id: finite-translation-augmentation-corner-has-every-matrix-width
kind: claim
title: Full finite-translation augmentation corners admit every prescribed local matrix width
distinct_from:
  affine-frobenius-group-has-almost-full-simple-block: that treats the almost-full block for an odd prime translation group; this gives explicit full-corner matrix units over every finite field and unital matrix embeddings of every prescribed width.
  noncentral-frobenius-negative-corner-is-rational-matrix-algebra: that uses the negative projection of one involution and produces power-of-two matrix sizes; this uses the complete augmentation complement of an arbitrary finite translation subgroup.
artifacts:
  - research/artifacts/noncentral-frobenius-negative-rational-matrix-corner-2026-09-08.md
---

Let `k=F_(p^r)`, `F=k_add semidirect k^times`, and let
`E=k_add` be its translation subgroup. Put

```text
Q_E=1-(1/|E|) sum_(e in E) e.
```

Then the entire corner is a full matrix algebra:

```text
Q_E C[F] Q_E ~= M_(p^r-1)(C).
```

Explicit finite-support matrix units are
`f_a m_(b/a) f_b`, indexed by nonzero `a,b in k`, where
`f_a` are the additive Fourier projections with coefficients
in `Q(exp(2 pi i/p))`. Their diagonal sum is `Q_E`, and
the normalized canonical corner trace is the matrix trace.

For every `D>=1`, choose `p` coprime to `D` and
`r=2 phi(D)`. Then `D` divides `p^r-1`, and matrix
amplification gives an explicit unital star embedding

```text
M_D(C) -> Q_E C[F] Q_E.
```

The unit is the full augmentation complement, not a selected
irreducible type of `E`. In every C-star representation of any
ambient group containing `E`, its image vanishes exactly when
the representation kills every element of `E`; normality in
that ambient group is unnecessary.

This establishes exact local matrix storage with an authenticated
finite-subgroup unit. It does not construct a global `B_loop`
corner map or its cross-context identities.

DERIVATION
finite-field-augmentation-fourier-matrix-proof
