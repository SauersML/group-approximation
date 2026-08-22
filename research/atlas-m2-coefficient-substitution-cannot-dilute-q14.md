---
rg: 2
id: atlas-m2-coefficient-substitution-cannot-dilute-q14
kind: claim
title: Approximate matrix-unit substitutions of the multiplicity-two escape retain a one-eighth q14 rank wall
distinct_from:
  atlas-packet-collision-m2-has-full-coefficient-algebra: that identifies the exact coefficient algebra and the failing q14 element; this rules out growing-width deformations obtained by approximately representing that coefficient algebra.
  atlas-fixed-formal-toeplitz-microstates-promote: that treats one fixed Laurent symbol and all Atlas residuals; this uses rank stability of the finite coefficient algebra M2 and gives the sharp q14 wall for the known escape phase.
  atlas-left-ideal-rank-nonwandering: that allows arbitrary nonstationary chart changes; this excludes only deformations which retain the approximate M2 multiplication table.
---

ESTABLISHED.  Let `U in GL_4(M_2(F2))=GL_8(F2)` be the exact
multiplicity-two packet-collision escape `(PCM1)`.  Let

```text
phi_n:M_2(F2) -> M_(d_n)(F2)                         (MCS1)
```

be unital linear maps whose four matrix-unit images satisfy the `M_2`
multiplication table with normalized-rank defect tending to zero.  Form the
block substitutions

```text
U_n=(id_(M4) tensor phi_n)(U).                        (MCS2)
```

Allow `o(d_n)` rank changes to make `U_n` invertible or to replace its
formal inverse by the substituted blocks of `U^(-1)`.  Then the packet and
collision residuals are `o(d_n)`, but q14 satisfies

```text
liminf rank(q14(U_n)-1)/(4d_n) >= 1/8.                (MCS3)
```

In particular, replacing the scalar `2 by 2` coefficient entries of the
known escape by shift/wrap matrices cannot produce the desired growing-width
countermodel if those replacements asymptotically obey the matrix-unit
relations.

### Proof

By Bauer--Blachar--Greenfeld finite-dimensional-algebra rank stability,
recorded in `atlas-rank-stability-literature-fence`, the approximate maps
`phi_n` are flexibly `o(d_n)`-close to exact unital representations of
`M_2(F2)`.  Up to an `o(d_n)` dimension change and conjugacy, every such
representation is the standard amplification

```text
M_2(F2) -> M_2(F2) tensor I_(k_n).                    (MCS4)
```

Fixed block polynomials are rank-Lipschitz, so all substituted word values
are `o(d_n)`-close to their exact amplifications.  The stored witness has
all twelve packet cubes and collision equal to one.  Its q14 defect has
binary rank one, as certified by
`atlas-multiplicity-two-joint-kernel-slice-is-empty`.  Under `(MCS4)` that
defect has rank `k_n` on total dimension `8k_n`, hence normalized rank
exactly `1/8`.  Stable `o(d_n)` changes alter normalized rank by `o(1)`,
which proves `(MCS3)`.

The hypothesis is load-bearing.  A genuine countermodel must make the
coefficient multiplication table itself fail on moving low-rank directions,
while the thirteen Atlas word polynomials still cancel those failures.  It
cannot be a functorial or approximate-algebra amplification of the known
`M_2` phase.
