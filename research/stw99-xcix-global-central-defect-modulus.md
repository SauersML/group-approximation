---
rg: 2
id: stw99-xcix-global-central-defect-modulus
kind: claim
title: Z-stability is the zero set of a Kadison--Kastler Holder centrality modulus
artifacts:
  - research/artifacts/stw99-xcix-quantitative-audit-2026-08-30.md
distinct_from:
  stw99-xcix-fixed-centrality-windows-collapse-at-zero-distance: that bounds each fixed finite window separately; this packages all window sizes into one scalar, identifies its zero set exactly, and proves a symmetric metric comparison whenever one side contains a unital copy of Z.
---

Fix a dense sequence `(z_j)` in the unit ball of `Z`, with `z_1=1_Z`.
For a unital C*-algebra `E`, let `Delta_(m,k)(E)` be the finite-window
defect from `stw99-xcix-fixed-centrality-windows-collapse-at-zero-distance`
and define

```text
kappa_Z(E)=sup_(m,k>=1) Delta_(m,k)(E) in [0,2],       (K1)
```

where the infimum over an empty set of unital embeddings is declared to be
`2`.

For every separable unital `E`,

```text
kappa_Z(E)=0  iff  E is Z-stable.                     (K2)
```

Moreover, let `A,B` be unital C*-subalgebras of one `B(H)` with a common
unit and

```text
d_KK(A,B)<gamma<1/12600000.
```

If either `A` or `B` contains a unital copy of `Z`, then both do and

```text
|kappa_Z(A)-kappa_Z(B)|
 <= 304 sqrt(gamma)+2 gamma.                          (K3)
```

In particular, if `A` is separable and Z-stable, then

```text
kappa_Z(B) <= 304 sqrt(gamma)+2 gamma.                (K4)
```

Thus failure of uniform openness in Problem XCIX through unital separable
pairs would produce non-Z-stable algebras `B_n` with

```text
0<kappa_Z(B_n)->0.
```

The remaining problem is therefore a genuine failure of a uniform positive
gap at the zero set of this scalar modulus.  The estimate proves continuity
with an explicit square-root modulus; it does not prove that zero is an open
value.
