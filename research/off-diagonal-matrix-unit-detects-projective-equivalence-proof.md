---
rg: 2
id: off-diagonal-matrix-unit-detects-projective-equivalence-proof
kind: route
title: Conjugate one Pauli matrix through the two carrier sheets
target: two-sheet-projective-closure-forces-equivalent-carriers
requires:
  - pauli-swap-coherence-reduces-to-the-commutant-gate
---

Use the matrix units `e_ij` of the sheet factor. Direct block
multiplication gives

```text
A_g(e_01 tensor I_d)A_g^*
 =e_01 tensor pi_0(g)pi_1(g)^*.                         (ODP1)
```

If `Ad(A_g)` preserves `B=M_2(C) tensor I_d`, the right side of `(ODP1)`
must belong to `B`. Hence there is a scalar `c_g in S^1` with

```text
pi_0(g)pi_1(g)^*=c_g I_d,
pi_1(g)=conj(c_g)pi_0(g).                               (ODP2)
```

Since both `pi_i` are representations, equation `(ODP2)` for `gh` shows

```text
c_(gh)=c_g c_h.
```

Thus `chi(g)=conj(c_g)` is a character and `(TPC1)` follows.

Conversely, if `(TPC1)` holds, then `(ODP1)` is a scalar multiple of
`e_01 tensor I_d`. The same is true for `e_10`, while the two diagonal
matrix units are fixed. Therefore `Ad(A_g)(B)=B`.

For `M>=3`, `GL_M(F_2)=SL_M(F_2)` and is perfect. One direct proof uses
elementary matrices:

```text
x_ij(1)=[x_ik(1),x_kj(1)]
```

for distinct `i,j,k`, and these transvections generate the group. Every
character is therefore trivial. After a fixed intertwining identification
of equivalent sheets,

```text
A_g=I_2 tensor pi_0(g),
```

which commutes with `B`.

The calculation also proves the negative statement. If the sheets are
inequivalent, the operator coefficient
`pi_0(g)pi_1(g)^*` in `(ODP1)` is nonscalar for some `g`. Products of
full generators then leave `B` before their projective Pauli rotations can
be multiplied. No map to `PU(2)=SO(3)` can be extracted by simply
discarding the carrier matrices.
