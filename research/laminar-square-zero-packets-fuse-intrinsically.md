---
rg: 2
id: laminar-square-zero-packets-fuse-intrinsically
kind: claim
title: A finite laminar packet of square-zero ideals fuses inside the original algebra
distinct_from:
  finite-square-zero-packets-admit-cutdown-fusion: that asks for arbitrary finite packets under the Global Glimm hypothesis; this proves exact fusion when packet ideals are pairwise comparable or disjoint.
  chain-ideal-lattice-solves-lxxiii: that assumes every pair of ambient ideals is comparable; this permits incomparable packet ideals when their intersection is zero.
artifacts:
  - research/artifacts/stw99-lxxiii-lxvi-focused-audit-2026-08-31.md
---

**ESTABLISHED.**  Let `A` be a C-star algebra and let
`x_1,...,x_n in A` satisfy `x_i^2=0`.  Put `I_i=Ideal(x_i)` and suppose that
for every `i,j` one has

```text
I_i subset I_j,       or       I_j subset I_i,       or       I_i intersect I_j=0.  (LF1)
```

Then there is an explicit square-zero `x in A` such that

```text
Ideal(x)=I_1+...+I_n.                                                     (LF2)
```

Choose one index from each distinct maximal member of the finite family
`{I_i}` and call the resulting set of indices `M`.  Two distinct ideals
`I_j,I_k`, with `j,k in M`, cannot be comparable, by maximality and the
choice of one representative per equality class.  Hence (LF1) gives
`I_j intersect I_k=0`.  Closed ideals in a C-star algebra satisfy

```text
I_j I_k subset I_j intersect I_k=0.
```

Set `x=sum_(j in M) x_j`.  Every mixed product vanishes, and therefore

```text
x^2=sum_j x_j^2 + sum_(j!=k) x_j x_k=0.                                  (LF3)
```

The same orthogonality gives

```text
x*x=sum_(j in M) x_j*x_j.
```

For a finite sum of positive elements, the generated ideal is the sum of
their generated ideals.  Also `Ideal(x_j*x_j)=Ideal(x_j)` and
`Ideal(x*x)=Ideal(x)`.  Consequently

```text
Ideal(x)=sum_(j in M) I_j=sum_(i=1)^n I_i,
```

because every member of the finite family is contained in a maximal one.
This proves (LF2) with no stabilization, approximation, or loss of support.
