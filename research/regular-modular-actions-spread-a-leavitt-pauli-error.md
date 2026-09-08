---
rg: 2
id: regular-modular-actions-spread-a-leavitt-pauli-error
kind: route
title: Rotate one regular-factor fiber and bound invariant containment by its coordinate support
target: frozen-leavitt-curvature-has-no-small-invariant-hull
requires:
  - leavitt-has-an-explicit-finite-c-killing-certificate
artifacts:
  - research/artifacts/frozen-leavitt-pauli-curvature-and-saturation-2026-09-08.md
---

Use the regular representation of `G=PSL_2(F_p)`, for primes `p>=5`,
and two ancillary two-dimensional factors. The standard modular matrices
give an order-three actor `C` and an order-two actor `B_1` generating
the regular action. Ancillary Pauli `Z` matrices supply `B_2,B_3`, so
both marked finite factors have exactly regular multiplicities.

For `u=(e_1+e_s)/sqrt(2)`, rotate `B_2` from `Z` to `Y` on
`u tensor C^2 tensor e_+`. This conjugation commutes with `B_1,B_3`,
preserving all required factor identities and multiplicities. If
`T=C B_1 C^(-1)`, then `u` and `Tu` are orthogonal. Direct multiplication
gives `d=[B_2,T]` equal to `iX` and `-iX` on the two corresponding
fibers. Thus `d^2=I-2F` for a rank-four projection `F`.

The certificate definition `j=a(CdC^(-1))a^(-1)` holds as a literal
word, so `j^2=I-2P`, where `P=a C F C^(-1)a^(-1)` still has rank
four. The support of `P` occupies at most twelve group coordinates.

If `E` contains `P` and commutes with `C,B_1`, it commutes with the whole
regular action. Its diagonal fiber traces are consequently constant.
Writing `chi_S` for the at-most-twelve-coordinate support gives

```text
4=Tr(P) <= Tr(chi_S E chi_S)
         =|S| rank(E)/|G| <= 12 rank(E)/|G|.
```

Since `n=4|G|`, this proves `rank(E)>=n/12`. After padding, apply the
same argument to the positive compression of `E` onto the original
summand; its trace is at most `rank(E)`.

The artifact computes all norm constants, explicitly exhibits the cheap
actor-changing repair, and separates this one-relator construction from
the unresolved full nine-word gap.
