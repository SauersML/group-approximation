---
rg: 2
id: schur-packet-child-square-is-pauli-transverse-proof
kind: route
title: Correct the two last generators and decompose the relative two-by-two algebra
target: schur-packet-child-square-is-pauli-transverse
requires:
  - schur-complement-controls-relative-pauli-module
---

Fix `x`.  The corrected involution `P_x` from `(SCP4)` belongs to the sector
algebra of `B_f^P`, because it is `p_(N+1)` times a product of leading
`p_i` generators.  It commutes with the full baseline algebra `M_D` and is
independent of it.  Therefore adjoining it gives

```text
C[B_f^P]_x=M_D tensor C[P_x]=M_D tensor C[C_2].
```

The same argument with `Q_x` gives the second identity in `(SPS2)`.  Equation
`(SCP7)` says that the two relative involutions commute when `f(x)=0` and
anticommute when `f(x)=1`.  Two independent commuting involutions generate
`C[C_2 x C_2]`; two anticommuting involutions generate `M_2`.  This proves
`(SPS3)`.

On a forbidden simple block choose the Pauli coordinates so that
`P_x=Z` and `Q_x=X`.  After suppressing the baseline factor, the four
Hilbert--Schmidt orthogonal coefficient spaces in the `A_f`-commutant are

```text
C I tensor M_m,  C X tensor M_m,
C Y tensor M_m,  C Z tensor M_m.                                (SPS6)
```

The `B_f^P` commutant is the sum of the `I` and `Z` spaces, the `B_f^Q`
commutant is the sum of the `I` and `X` spaces, and the `B_f` commutant is
the `I` space.  Write `Y=Y_I+Y_X+Y_Y+Y_Z` according to `(SPS6)`.  Then

```text
||Y-E_B Y||_2^2 = ||Y_X||_2^2+||Y_Y||_2^2+||Y_Z||_2^2,
||Y-E_P Y||_2^2 = ||Y_X||_2^2+||Y_Y||_2^2,
||Y-E_Q Y||_2^2 = ||Y_Y||_2^2+||Y_Z||_2^2.
```

The last two quantities sum to the first plus `||Y_Y||_2^2`, proving
`(SPS4)`.  The descriptions and dimensions in `(SPS5)` are immediate.

For `(SPS7)`, write `m_(x,lambda)` for the external multiplicities of the
forbidden full-packet simples.  Their total forbidden Hilbert dimension is

```text
q d=2D sum_(x,lambda) m_(x,lambda).
```

The two centered child modules have total dimension
`2 sum_(x,lambda) m_(x,lambda)^2`.  There are at most `K L` summands, so
Cauchy--Schwarz gives

```text
2 sum m_(x,lambda)^2
 >= 2 (q d/(2D))^2/(K L)
 = q^2 d^2/(2D^2 K L).
```

Divide by `d^2`.

