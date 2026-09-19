---
rg: 2
id: kt-payload-annihilator-mixed-return-has-profinite-countermodels
kind: claim
title: The payload-annihilated Kun--Thom moved-site return has exact profinite countermodels
distinct_from:
  kt-single-root-mixed-return-has-exact-finite-countermodels: That retains the marked lamp separation by imposing only the cyclic root stabilizer; this imposes the full Gamma stabilizer packet, so the finite model collapses the two sites, and shows that multiplying the collapsed difference by the bounded-type payload still gives no payment.
  profinite-free-compressors-retain-coefficient-residual: That retains a named base coefficient under the two free covariance rows without lamps; this adds the smallest Gamma-stabilizer-sensitive moved-site expression and proves that every annihilator-oriented payload coupling is still absorbed.
  exact-expander-a5-carriers-collapse-marked-center: That gives a Kazhdan estimate for an already classical finite actor carrier; this constructs an exact unitary regular model in which the coefficient residual stays positive precisely because the moved-site difference has collapsed to zero.
---

**ESTABLISHED MIXED-RETURN FENCE.**  Use the pinned Kun--Thom pair and the
explicit words

```text
r=e_12(x_1) in Gamma,
h=LrL^(-1)=e_12((x_1x_2x_3)^(-1)),                    (PAM1)
```

where `L` is a word in the opposite compressors `A,B`.  Let `ell` be a
binary base lamp and impose the full finite Kazhdan stabilizer packet

```text
[ell,s]=1,                 s in K_Gamma,               (PAM2)
```

where `K_Gamma` is the packet from
`kt-elementary-kazhdan-packet-rounds-base-lamp`.  Since it generates
`Gamma`, `(PAM2)` makes `ell` commute with `Gamma` in every exact model.

Let `z` be a nonzero projection in a fixed finite payload packet algebra,
and let `a in C[Gamma]` be any fixed algebraic coefficient.  The smallest
payload-conditioned moved-site annihilator is

```text
M=z(1-a)(ell-h ell h^(-1)).                            (PAM3)
```

Equivalently one may replace the last difference by `[ell,h]`, up to a
unitary right factor.  Then, for every finite actor word window and every
finite support window for `a`, there is an exact finite-dimensional unitary
model satisfying all actor relations, `(PAM2)`, and

```text
M=0,                                                   (PAM4)
```

while

```text
||z(1-a)||_2
 =sqrt(tau_packet(z)) ||lambda_Gamma(1-a)||_2.         (PAM5)
```

The actor window can simultaneously have canonical regular trace.  If `a`
is the bounded-type approximation with `||a-p_<=K||_max<=epsilon`, then

```text
||z(1-a)||_2 >=(1-epsilon)sqrt(tau_packet(z)).          (PAM6)
```

Thus neither property `(T)`, the full Gamma stabilizer rows, the arithmetic
return `(PAM1)`, nor their product with the residual `z(1-a)` yields a
normalized-HS payment when the coupling is oriented as an annihilator.

## Why the countermodel is compatible with the perfect trace

If `z` is a forbidden payload projection, the perfect tracial BCS model has
`z=0`.  Tensoring it with the canonical Kun--Thom wreath gives an exact
infinite tracial model in which `(PAM3)` vanishes although the two lamps
`ell` and `h ell h^(-1)` are distinct.  In the finite countermodels the
opposite mechanism occurs: `z` has its positive regular trace, but finite
quotient blindness puts the image of `h` back in the image of `Gamma`, so
the two lamps are equal.  The same mixed row is therefore vacuous at both
ends for two different reasons.

This double vacuity is the exact failure mode of the most direct
payload-sensitive return.  Any successful relation must be
**reflective rather than annihilating**: on the active payload it must
recover a fixed portion of `z(1-a)` from the moved-site difference and must
therefore prevent the profinite site collapse.  Constructing such a
dimension-uniform reflection while keeping the `z=0` perfect completion is
the same surviving kernel-reflection/actor-classicalization gate; merely
multiplying the moved-site commutator by the forbidden coefficient does not
advance it.

DERIVATION
kt-payload-annihilator-profinite-countermodel-proof
