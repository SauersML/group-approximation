---
rg: 2
id: bs14-monodromy-root-quantization-proof
kind: route
title: Round each scalar return phase and alter only its closing shift edge
target: bs14-monodromy-admits-root-of-unity-quantization
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
---

Use `bs14-unitary-representations-are-periodic-cycle-packets`.  Simultaneously
diagonalizing each multiplicity monodromy splits the representation into
scalar packets.  On one scalar packet of length `m`, choose bases so that
`S` is diagonal along one fourth-power orbit and `R` is the cyclic shift
whose closing edge has phase `v`; equivalently `R^m=v`.

Choose an `M`th root of unity `w` nearest to `v` and replace only that closing
edge by `w`.  Scalar edge phases cancel in conjugation, so the resulting
packet still satisfies `(BMQ1)` exactly, while its return phase obeys
`w^M=1`.  The angular distance from `v` to `w` is at most `pi/M`, hence

```text
|v-w| <= pi/M.                                        (BMR1)
```

If there are `p` scalar packets, their altered closing edges are orthogonal
matrix entries.  Since every packet has positive dimension, `p<=d`, and
therefore

```text
||R-R_M||_2^2
 = d^(-1) sum_(packets) |v-w|^2
 <= p pi^2/(d M^2)
 <= pi^2/M^2.                                         (BMR2)
```

This proves `(BMQ2)`.

For `(BMQ3)`, fix one spectral orbit `O` of minimal length `m` and list its
scalar packets by `a`.  In the basis `e_(j,a)`, `j in Z/m`, the `O`-part of
`{S}'` is spanned by matrix units

```text
E_(j;a,b)=|e_(j,a)><e_(j,b)|.
```

After `m` applications of `Ad(R_M)`, this matrix unit is multiplied by
`w_a conjugate(w_b)`, an `M`th root of unity.  Hence `Ad(R_M)^(mM)` is the
identity on the whole orbit block, including all `a!=b` directions.
