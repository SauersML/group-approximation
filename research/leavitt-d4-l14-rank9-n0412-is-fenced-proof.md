---
rg: 2
id: leavitt-d4-l14-rank9-n0412-is-fenced-proof
kind: route
title: Use the unique copy-two syllable to trivialize all five 0;412 branches
target: leavitt-d4-l14-rank9-n0412-is-fenced
requires:
  - leavitt-d4-l14-seven-syllable-splitter
---

Choose the actual start-5, size-`241` representative of cyclic key `0;412`.
Its exact equations are

```text
H A0=E5^-1H^-1,
H^-1C0=A1^-1H^-1,
H^-1C1=E7^-1 H E6^-1 H,
K=H^-1B0 H^-1B1 H E1 H^-1E2 H E3 H^-1E4.
```

Use the notation from the preceding length-fourteen proofs.  In branch I,
the first equation gives

```text
H=e_3, a=b=1, c=e^2, d=p^-1e^-2.
```

The third equation contains the unique copy-2 syllable `e^-1_2`, while its
left side contains no copy-2 syllable.  Hence `e=1`; the remaining copy-0
equation is `p=vw`.  The boundary is `K=p^-1vw=1`.

In branch II the same unique-copy-2 argument again gives `e=1`.  Normal-form
matching then yields

```text
cp=v, d=v^-1, z=pv^-1, c=vp^-1,
```

and the boundary reduces to `K=cz=1`.  Branch III likewise forces `e=1`
and then `p=w`; its boundary is `K=p^-1zz^-1w=1`.

In branches IV and V, the first equation again reduces `H` to a single
copy-3 syllable.  The third equation has the form

```text
e^-1_3(ep)_0
 =u^-1_0(ep)^-1_1 e_3e^-1_2a^-1_1u_0e_3.
```

Its unique copy-2 syllable forces `e=1`; the remaining equations give
`ep=1` and `a=1`.  Branch IV has the additional relation `xy=p` and boundary
`K=p^-1_3x_3y_3=1`.  Branch V has `x=p` and boundary
`K=p^-1_3p_3v_0v^-1_0=1`.  Thus all five exhaustive branches have trivial
boundary.

