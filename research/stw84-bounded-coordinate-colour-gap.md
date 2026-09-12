---
rg: 2
id: stw84-bounded-coordinate-colour-gap
kind: claim
title: Bounded coordinate colourings cannot repair weighted Fourier rows
distinct_from:
  stw84-weighted-fourier-cutdown-and-row-gap: that theorem gives a fixed gap for repairing one unsplit matrix row by one order-zero map; the present theorem permits an arbitrary partition of the Fourier coordinates and proves a gap for every fixed number of coordinate colours.
artifacts:
  - research/artifacts/stw84-coordinate-colouring-firewall-2026-08-30.md
---

Let `A` be a unital C-star algebra and let `h in A` be a norm-one positive
contraction.  For `n>=1`, define the diagonal weighted averaging map

```text
Lambda_(h,n):C^n->A,
Lambda_(h,n)(z_0,...,z_(n-1))
 =n^(-1)(sum_i z_i)h.                                  (CCF1)
```

Fix `d>=1`, partition the coordinate set into at most `d` sets

```text
{0,...,n-1}=S_1 disjoint_union ... disjoint_union S_d,
```

and regard `C^n=directSum_c C^(S_c)` as a `d`-coloured finite-dimensional
algebra.  If

```text
Psi_c:C^(S_c)->A
```

are c.p.c. order-zero maps and `Psi=directSum_c Psi_c`, then, whenever
`n>=2d`,

```text
||Lambda_(h,n)-Psi|| >= 1/(16d^2).                    (CCF2)
```

More exactly, if `m=max_c |S_c|`, then

```text
||Lambda_(h,n)-Psi||
 >= floor(m/2)ceil(m/2)/(2n^2).                       (CCF3)
```

Now let `U in A` be unitary and let `Theta_(h,n):M_n->A` be the canonical
weighted Fourier row from
`stw84-weighted-fourier-cutdown-and-row-gap`:

```text
Theta_(h,n)([c_ij])
 =n^(-1)sum_(i,j)c_ij h^(1/2)U^iU^(-j)h^(1/2).
```

Its restriction to the diagonal is exactly `Lambda_(h,n)`.  Consequently
`(CCF2)` applies to every proposed repair which first divides the Fourier
coordinates into at most `d` interval blocks, congruence classes,
checkerboard packets, or arbitrary disjoint coordinate packets, and then
uses one order-zero return map per colour.  It also applies on the scalar
diagonal of coefficient-valued matrix stages `M_n(D)`.

Thus no fixed coordinate colouring of the standard band-matrix
factorization can converge in return-map norm as the requested tolerance
tends to zero.  Any successful bounded-colour construction must mix or
duplicate coordinates already in the incoming c.p. map, or replace the
canonical weighted row by return maps whose diagonal supports are not all
scalar multiples of the same carrier.  The theorem does not obstruct such
non-coordinate factorizations.
