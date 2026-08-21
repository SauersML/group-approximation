---
rg: 2
id: exact-codensity-does-not-imply-matricial-rcc
kind: claim
title: Exact finite-dimensional co-density does not imply matricial relative-commutant collapse
artifacts:
  - research/artifacts/sl3-projective-rcc-audit-2026-08-21.md
distinct_from:
  exact-projective-codensity-has-a-uniform-trace-square-gap: that is an exact finite-dimensional theorem; this shows that even its strongest image-equality hypothesis has no automatic tracial-ultraproduct extension.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that conditionally refutes a specific arithmetic RCC pair via a CE action; this gives an unconditional non-arithmetic countermodel to the abstract implication.
  projective-transfer-equals-rcc-for-perfect-pairs: that identifies projective and ordinary transfer once a qualitative ultraproduct theorem is available; this shows exact finite-dimensional co-density cannot supply that theorem by itself.
---

There is a finitely generated perfect Kazhdan group `C` inside a countable
perfect hyperlinear group `A` such that every finite-dimensional unitary
representation `rho` of `A` satisfies

```text
rho(A)=rho(C),
```

but relative-commutant collapse fails maximally in the canonical regular
tracial model of `A`.

Take

```text
C = SL_3(Z),       D = A_fin,       A = C x D,
```

where `A_fin` is the finitary alternating group on a countable set. Every
finite-dimensional unitary representation of the infinite simple locally
finite group `D` is trivial. Hence exact finite-dimensional image equality
holds. Nevertheless, for noncommuting `x,y in D`, the regular-model unitary
`u=1 tensor lambda_D(x)` commutes with `C`, whereas for `h=(1,y)`,

```text
[u,lambda_A(h)] = 1 tensor lambda_D([x,y])
```

has trace zero. In particular its projective trace-square energy is one.

Thus exact co-density, perfectness, and property (T) of the subgroup do not
control approximate/tracial-ultraproduct relative commutants. A proof for
the arithmetic `SL_3` pair must use arithmetic coupling absent from a direct
product, not only equality of exact finite-dimensional images.

