---
rg: 2
id: leavitt-d4-l14-rank9-n2115-is-fenced-proof
kind: route
title: Fence all five branches of the normal 2;115 class
target: leavitt-d4-l14-rank9-n2115-is-fenced
requires:
  - leavitt-d4-l14-seven-syllable-splitter
---

Use the actual start-3, size-`151` representative.  Its carrier equations and
boundary are

```text
H A0=E3^-1H^-1,
H^-1C0=A1^-1H^-1,
H^-1C1=E4^-1H,
K=H^-1B0 H^-1B1 H E5 H^-1E6 H^-1E7 H E1 H^-1E2.
```

Retain the notation of the `0;115` proof and put `x=g3`.  In branch I, the
nonidentity carrier case has `e^2=1`, `p=w=1`, and

```text
K=e_3e_0e_3e_1(v^-1u^-1)_0e_2e_3(uv)_0.
```

The other carrier case has `e=1,p=w^-1` and `K=1`.  In branch II the
nonidentity case is

```text
e^2=1, c=p^-1, d=1, z=e p^-1e,
K=e_3e_0(p^-1e)_3e_1p_3(uv)^-1_0e_2e_3(uv)_0;
```

again `e=1` gives `K=1`.  Branch III similarly has identity boundary when
`e=1`; otherwise

```text
e^2=1, cp=1, w=d=1, z=epe,
K=e_3e_0(p^-1e)_3e_1u^-1_0e_2e_3u_0p_3.
```

Every displayed nonidentity case has a unique nontrivial copy-2 syllable and
a nonvanishing right tail, so none is a one-copy word.

For branch IV, write the surviving involution as `b`.  The identity case is
again immediate; the other case has

```text
K=b_3b_0(p^-1b)_3b_1(p b x^-1b)_3u^-1_0
  b_2b_3u_0(bxb)_3.
```

For branch V the corresponding word is

```text
K=b_3b_0b_3b_1(bx^-1b)_3u^-1_0b_2b_3u_0(bxb)_3.
```

In each word `b_2` is the unique copy-2 syllable.  If its right tail does not
vanish, the boundary is visibly not one-copy.  If that tail vanishes, the
left side still contains the unique nontrivial `b_1`, so the prefix cannot
vanish and the whole word still cannot lie in copy 2.  This exhausts all five
branches and fences the class.

