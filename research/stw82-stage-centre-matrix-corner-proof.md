---
rg: 2
id: stw82-stage-centre-matrix-corner-proof
kind: route
title: Reuse every ideal colour through lifted matrix units at each AF stage
target: stw82-af-split-stage-centres-obey-maximum
requires: []
artifacts:
  - research/artifacts/stw82-stage-centre-split-audit-2026-08-30.md
---

For each stage in `(SC2)`, set

```text
E_n=I+s(D_n).
```

This is a C*-subalgebra of `E`, and the union of the `E_n` is dense.  Write

```text
D_n=direct_sum_(j=1)^k M_(r_j),
```

let `z_j` be the central unit of the `j`th block, and put `p_j=s(z_j)`.
The projections `(p_j)` are orthogonal and sum to `1`.  They commute with
`s(D_n)` because the `z_j` are central in `D_n`, and commute with `I` by
`(SC3)`.  Hence they are central in `E_n=I+s(D_n)`, and

```text
E_n=direct_sum_j p_jE_n,
I=direct_sum_j p_jI.                                  (SM1)
```

Fix `j` and lift standard matrix units of `M_(r_j)` to

```text
f_(ab)=s(e_(ab)) in p_jE_n.
```

They form a unital system of matrix units in the corner `p_jE_n`.  Put

```text
B_j=f_(11)E_nf_(11),       J_j=f_(11)If_(11).          (SM2)
```

The standard matrix-unit isomorphisms give

```text
p_jE_n  ~= M_(r_j)(B_j),
p_jI    ~= M_(r_j)(J_j).                              (SM3)
```

For completeness, the first map sends `x` to

```text
(f_(1a) x f_(b1))_(a,b),
```

with inverse `(b_(ab)) |-> sum_(a,b) f_(a1)b_(ab)f_(1b)`; ideality gives
the second identification.

The quotient of `B_j` by `J_j` is the one-dimensional corner
`e_(11)M_(r_j)e_(11)`.  More precisely, if `b in B_j`, then
`q(b)=lambda e_(11)` for a scalar `lambda`, and

```text
b-lambda f_(11) in J_j.
```

Since `q(f_(11))` is nonzero,

```text
B_j=J_j+C f_(11)=unitization(J_j).                    (SM4)
```

Nuclear dimension is invariant under matrix amplification and minimal
unitization.  Equations `(SM3)--(SM4)` therefore imply

```text
dim_nuc(p_jE_n)=dim_nuc(J_j)=dim_nuc(p_jI).            (SM5)
```

Using finite-direct-sum permanence in `(SM1)` gives

```text
dim_nuc(E_n)=max_j dim_nuc(p_jI)=dim_nuc(I).           (SM6)
```

If `dim_nuc(I)` is finite, local/inductive-limit permanence for the dense
union of the `E_n` yields `dim_nuc(E)<=dim_nuc(I)`.  Ideal monotonicity
gives the reverse inequality.  If `dim_nuc(I)=infinity`, ideal monotonicity
already forces equality.  Finally `D` is AF, so `dim_nuc(D)=0`, proving
`(SC4)`.

The proof pinpoints the missing-colour mechanism.  Full commutation of
`s(D_n)` with `I` is unnecessary: lifted matrix units are used as exact
Morita coordinates, not as central supports.  Only the block-unit
projections must commute with `I`, so that different simple quotient blocks
split before the matrix-corner calculation.
