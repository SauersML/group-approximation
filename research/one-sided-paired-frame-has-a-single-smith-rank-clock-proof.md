---
rg: 2
id: one-sided-paired-frame-has-a-single-smith-rank-clock-proof
kind: route
title: Smith reduction of the one-sided paired commutator map
target: one-sided-paired-frame-has-a-single-smith-rank-clock
requires:
  - paired-frame-moving-kernel-is-a-rank-one-veronese-clock
  - alternating-free-ring-shears-have-strict-degree-drift
---

Put `W=wedge^2(R^4)` in the coordinate order
`(01,02,03,12,13,23)`.  The source and coefficient halves of the level-zero
paired commutator map are split surjections `W -> R^3` with the same kernel

```text
K_0=span_R{e_01,e_13,e_23}.                                (OSP1)
```

Transporting the source generators by `T^(-n)` precomposes its commutator
map by `wedge^2(T^(-n))`.  Its kernel is therefore
`wedge^2(T^n)K_0=K_n`; the coefficient kernel remains `K_0`.  The combined
kernel is their intersection.  The moving-kernel theorem gives

```text
K_n=span_R{e_01,e_23} direct_sum R v_n,
v_n=c_n^2 e_02+c_nd_n(e_03+e_12)+d_n^2e_13.              (OSP2)
```

Since `c_n` is nonzero for `n>=1`, `Rv_n` meets `Re_13` trivially.  This
proves `(OSR3)` and the rank assertions.

It remains to compute the integral, rather than fraction-field, invariant.
Use the split coefficient map to identify its three live columns
`(e_02,e_03,e_12)` with the standard basis of `R^3`.  Write

```text
S^(-n)=[[d_n,c_n],[c_n,a_n]],       a_nd_n+c_n^2=1.       (OSP3)
```

After invertible constant row changes in the source and coefficient centers,
the coefficient half of `C_n` is `[I_3 | 0]` on the four columns
`(e_02,e_03,e_12,e_13)`.  Subtracting polynomial multiples of those three
coefficient rows clears the first three source columns.  The remaining
source column is

```text
(c_n^2, c_na_n, c_na_n)^T.                                (OSP4)
```

The first three Smith invariants are units.  The fourth is the gcd of the
entries in `(OSP4)`:

```text
gcd(c_n^2,c_na_n,c_na_n)
 =c_n gcd(c_n,a_n)=c_n,                                   (OSP5)
```

because `(OSP3)` makes `c_n` and `a_n` coprime.  This proves `(OSR4)`.

Finally, the strict-degree recurrence for `S^n` gives that `c_n` is monic of
degree `2n-1`.  If an additive sign character is trivial below that degree,
all lower terms of `c_n` evaluate to `+1`, so its value on `c_n` equals its
value on the unique leading monomial.  This is exactly the first-detection
event used by the free-root boundary reservoir.

The companion computation also explains why symmetric transport is useless.
The contragredient character
`h_n=h_0 o wedge^2(T^(-n))` annihilates `K_n` identically.  The nonzero Smith
coordinate appears only in the one-sided comparison with the fixed
coefficient packet.
