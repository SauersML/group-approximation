---
rg: 2
id: affine-leavitt-p-heisenberg-hs-corner-blocker
kind: claim
title: Collapse the selected p-Heisenberg four-cap corner in normalized-HS microstates
distinct_from:
  affine-leavitt-p-heisenberg-graft-kills-fd-four-cap-corner: that is the exact finite-dimensional statement; this asks for its dimension-independent normalized-HS version.
  affine-leavitt-steinberg-hs-coefficient-decoder: that produces collapse of the native active root; this claim transfers that collapse through one fixed Heisenberg commutator and character average.
---

**OPEN.**  For the finite presentation of `G_p`, prove a modulus
`Omega(delta)->0` such that every normalized-HS `delta`-representation
satisfies

```text
||Q_chi(U)||_2 <= Omega(delta).                          (PHB1)
```

This follows directly from
`affine-leavitt-steinberg-hs-coefficient-decoder`.  Together with
`approximate-relative-leavitt-cell-kills-active-trace`, that decoder gives

```text
||w(U)-I||_2 <= eta(delta),             eta(delta)->0.   (PHB2)
```

If `C=U(c)`, the fixed relator `c=[w,z]` gives

```text
||C-I||_2 <= delta+2 eta(delta).                         (PHB3)
```

No spectral rounding is required.  Since the nontrivial character
coefficients sum to zero,

```text
e_chi(C)
 =(1/p) sum_(k=1)^(p-1) conjugate(chi(c))^k(C^k-I),

||e_chi(C)||_2
 <=(1/p)sum_(k=1)^(p-1)k||C-I||_2
 =((p-1)/2)||C-I||_2.                                  (PHB4)
```

The binary factor `(I-U(J))/2` is an operator-norm contraction, so

```text
||Q_chi(U)||_2
 <=((p-1)/2)(delta+2eta(delta)).                         (PHB5)
```

Thus the exact odd-sector graft adds no analytic loss beyond the explicit
constant `(p-1)/2`.

## Attempts

- **Use exact annihilation without decoding.**  `(PHG8)` follows, but exact
  root-kernel intersection has no dimension-independent HS modulus.  The
  only open step is still the affine-Leavitt root-to-coefficient decoder.
- **Round the `p`-th root first.**  This is unnecessary: `(PHB4)` applies to
  every unitary `C`, without using `C^p=1` or a spectral projection theorem.
