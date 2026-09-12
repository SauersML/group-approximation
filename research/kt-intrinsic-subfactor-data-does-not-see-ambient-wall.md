---
rg: 2
id: kt-intrinsic-subfactor-data-does-not-see-ambient-wall
kind: claim
title: The q=2 compressor inclusion has identical intrinsic subfactor data in two ambients with opposite commutant growth
distinct_from:
  kt-compressor-pair-group-factor-ultrapower-has-no-leak: that computes the relative commutants in the self-ultrapower ambient; this compares that ambient with the Clifford crossed product and extracts the resulting no-go for intrinsic subfactor invariants.
  clifford-compressor-site-growth: that computes the ambient commutant-growth index in the Clifford crossed product; this proves that the same abstract subgroup-factor inclusion has no growth in another exact finite tracial ambient.
  commutant-density-trace-blind: that kills normalized commutant dimension on regular-character microstates; this kills Jones index, the standard invariant, and every finite-moment invariant intrinsic to the embedded subgroup-factor inclusion, even before taking coordinates.
---

Fix the Kun--Thom pair over `F_2` with `d=3`, let `t` be a strict positive
compressor, put `Lambda=t Gamma t^(-1)<Gamma`, and denote the canonical
subfactor inclusion by

```text
P=L(Lambda) < N=L(Gamma).                                      (KIF1)
```

There are two trace-preserving embeddings of this **same** inclusion into
finite tracial von Neumann algebras with opposite ambient relative-commutant
behaviour.

1. In the constant copy inside `M_0=L(G)^omega`,

   ```text
   P' cap M_0 = N' cap M_0 = C.                                (KIF2)
   ```

2. In the canonical Clifford crossed product
   `M_Cl=Cl(G/Gamma) crossed_product G`,

   ```text
   N' cap M_Cl  <  P' cap M_Cl,
   [P' cap M_Cl : N' cap M_Cl]=infinity.                       (KIF3)
   ```

Moreover `[N:P]=[Gamma:Lambda]=infinity`.  Thus the Jones index of `(KIF1)`,
its standard invariant, its `P`--`N` bimodule data, and every other invariant
of the abstract tracial inclusion are literally identical in `(KIF2)` and
`(KIF3)`, while the ambient commutant-growth conclusion is opposite.

The obstruction is stronger at the finite-moment level.  Both ambient maps
restrict to the canonical trace-preserving inclusion `(KIF1)`.  Therefore
every joint tracial `*`-moment, every normalized `L^2` norm of a fixed
noncommutative polynomial in elements of `P` and `N`, and every continuous
functional of finitely many such data agrees in the two ambients.  No such
intrinsic, normalized-Hilbert--Schmidt-continuous statistic can prove
`P' cap M=N' cap M` for arbitrary matrix-ultraproduct ambients.

The ambient Pimsner--Popa index in `(KIF3)` does detect the wall, but it is
not a replacement: it quantifies over the ambient relative commutants rather
than over `(KIF1)`, and it is discontinuous under normalized-HS-small
refinements.  Hence a proof of `approximate-collapse-for-kt-compressor` must
use a property specific to the **matrix-ultraproduct realization of the
ambient complement** `L^2(M) minus L^2(L(G))`; finite index, the abstract
standard invariant, and subgroup-factor bimodule rigidity alone cannot
supply the missing range comparison.

