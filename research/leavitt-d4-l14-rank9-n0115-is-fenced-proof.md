---
rg: 2
id: leavitt-d4-l14-rank9-n0115-is-fenced-proof
kind: route
title: Eliminate all five seven-syllable branches in the normal 0;115 class
target: leavitt-d4-l14-rank9-n0115-is-fenced
requires:
  - leavitt-d4-l14-seven-syllable-splitter
---

Use the start-1, size-`151` representative and its exact carrier equations
and boundary from `leavitt-d4-l14-rank9-six-classes-proof`.  Put

```text
p=g1, u=g2, z=g3, v=g4, w=g6, d=g9, e=g10,
a=g11, b=g12, c=g13.
```

The common equation first gives `g0=1` and the five exhaustive branches of
the seven-syllable splitter.

In branches I and II, free reduction in the two remaining carrier equations
has

```text
H=a_0b_1(cpd)_2e_3, A0=(pd)_3, E1=1, E2=v_0.
```

Factor malnormality forces `H=e_3`, `a=b=1`, `cpd=1`, and `pd=e^-2`.
The last equation has exactly the two normal-form cases

```text
e=1, p=v^-1;                 or
e!=1, e^2=1, p=v=1.
```

In the first case direct substitution gives `K=1`.  In the second it gives

```text
K=e_3e_0e_3e_1u^-1_0e_2e_3u_0.
```

The nontrivial copy-2 syllable and the right tail `e_3u_0` exclude a
one-copy word.

Branch III has `E1=z_3,E2=1`.  Its two carrier equations force

```text
H=e_3, a=b=1, c=p^-1, d=1, e^2=1,
z=e p^-1e.
```

The boundary is

```text
K=e_3e_0(p^-1e)_3e_1p_3u^-1_0e_2e_3u_0.
```

It is the identity when `e=1`; otherwise the same unique-copy-2/right-tail
argument fences it.

In branch IV the exact reduction is

```text
H=e_3, a=b=1, d=1, c=p^-1, e^2=1,
z=e p^-1e,
K=e_3e_0(p^-1e)_3e_1p_3u^-1_0e_2e_3u_0,
```

so the branch-III argument applies verbatim.  In branch V, the carrier split
is either an identity-boundary case or the involutory case

```text
e^2=1, p=v=z=d=c=1,
K=e_3e_0e_3e_1u^-1_0e_2e_3u_0,
```

already fenced above.  The five branches exhaust the common equation, hence
the whole class is globally fenced.

