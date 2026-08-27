---
rg: 2
id: a4-regular-line-sector-spectral-split-proof
kind: route
title: The A4 character table gives compression eigenvalues 1 and 1/3
target: a4-regular-line-sector-spectral-split
requires: []
---

Use the four irreducible representations of `A4`: three one-dimensional
characters `xi_0,xi_1,xi_2`, on which `b` acts by `+1` and `a` acts by
`1,omega,omega^2`, and the three-dimensional irrep `V` with character values

```text
chi_V(1)=3,
chi_V(order 2)=-1,
chi_V(order 3)=0.
```

Fix a character `chi` of `<a>`.  Exactly one of the one-dimensional `A4`
characters restricts to `chi`; on that line `P_chi=1` and `Q_+=1`, so the
compression eigenvalue is `1`.

Now work in one copy of `V`.  The restriction of `V` to `<a>` has the three
distinct eigencharacters `1,omega,omega^2`, so `P_chi V` is one-dimensional.
The scalar of `P_chi rho(b) P_chi` on this line is its trace

```text
Tr_V(P_chi rho(b))
 = (1/3) sum_(r=0)^2 conjugate(chi(a^r)) chi_V(a^r b).
```

Here `b` has order `2`, while `ab` and `a^2b` have order `3` in the
`(2,3,3)` triangle group `A4`.  Therefore the character values are
`-1,0,0`, and the displayed scalar is `-1/3`, independently of `chi`.
Consequently

```text
P_chi Q_+ P_chi = (1 + (-1/3))/2 = 1/3
```

on the `V` contribution, and `P_chi Q_- P_chi=2/3` there.  On the line
character contribution the corresponding values are `1` and `0`.

Finally, in `Reg(A4)` each one-dimensional irrep occurs once and `V` occurs
with multiplicity `dim(V)=3`.  Thus inside each `P_chi` sector the eigenvalue
`1` has multiplicity one and `1/3` multiplicity three per regular copy.  Under
arbitrary regular amplification both multiplicities scale uniformly.  Since
the full regular dimension is `12`, the top spectral projection has normalized
trace `1/12`, and the spectral gap between `1` and `1/3` is `2/3` exactly.