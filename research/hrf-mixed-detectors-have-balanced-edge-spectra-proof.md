---
rg: 2
id: hrf-mixed-detectors-have-balanced-edge-spectra-proof
kind: route
title: Combine two reflections of the edge spectrum and count the even symmetric-power weights
target: hrf-mixed-detectors-have-balanced-edge-spectra
requires: []
artifacts:
  - research/artifacts/hrf-mixed-spectral-balance-2026-09-20.md
---

Negating the first pinned lift gives three determinant-one matrices
of trace 14 and characteristic polynomial `t^2-14t+1`, whose
discriminant is the nonsquare 2 in `F_19`. They are conjugate in
`GL_2(F_19)`. Their centralizer is `F_361^*`, with determinant the
surjective norm to `F_19^*`, so the conjugator can be corrected to
have determinant one. Their inverses have the same polynomial.
Hence all three edge classes are conjugate in `S` and are conjugate
to their inverses. Their eigenvalues in these lifts are primitive
fifth roots, as checked algebraically in Section 1 of the artifact.

Fix a primitive fifth root `eta` and let `n_i(j)` be the multiplicity
of `eta^j` at vertex `i` on this common edge class. Inversion gives
`n_i(j)=n_i(-j)`. If the scalar mark is `eta^t`, `t!=0`, an edge
with twist `d_il` gives `n_i(j)=n_l(j-s)`, `s=t d_il`.
For a nonzero edge, the latter identity and the reflection at vertex
`l` make `n_i` invariant under `j -> 2s-j`. Composing with
`j -> -j` makes it invariant under a nonzero translation of `F_5`.
It is therefore constant. The edge identities and connectedness
propagate constant multiplicity to every vertex. In every
characteristic other than five, cyclic edge restrictions are semisimple, and the conclusion
is exactly a direct sum of regular `C_5` modules.

Now specialize to characteristic 19. The standard defining-characteristic classification lists the
simple `S` modules as `L_r=Sym^r`, for even `0<=r<=18`; the
artifact records the precise university-repository research source for
this prior input. On the chosen natural lift, the eigenvalues
on `L_r` are `eta^(r-2i)`, `0<=i<=r`. Their multiplicities in
the order `1, each eta^±1, each eta^±2` are respectively

```
r:  0     2     4     6     8     10    12    14    16    18
   100   101   111   121   122   322   323   333   343   344.
```

Cyclic restriction is exact and semisimple, so these multiplicities
add across any vertex composition series. Equating the first and
third entries gives `n0+n10=n8+n18`. Equating the first and
second entries and subtracting that equality gives
`n2+n12=n6+n16`. Conversely these equalities make all three
entries equal, and inversion covers all five eigenvalues. This
proves both directions of the composition-vector assertion. No
Ext classification or computation is required.
