---
rg: 2
id: leavitt-d4-l14-rank9-i3115-is-fenced-proof
kind: route
title: Eliminate the five branches of inverse class 3;115
target: leavitt-d4-l14-rank9-i3115-is-fenced
requires:
  - leavitt-d4-l14-seven-syllable-splitter
---

Use the inverse face assignments of the `0;142` proof and the valence-seven
assignment

```text
T4=P, T5T6T0T1T2=C^-1, T3=R.
```

Then

```text
H^-1B0=E5^-1H^-1, H^-1C0=A1^-1H^-1,
H^-1B1=E4^-1H,
K=A0^-1H^-1C1^-1H E3^-1H^-1E2^-1H
  E1^-1H^-1E7^-1H E6^-1H.
```

In branch I, `B0=1` and `H=h_2`, where `h=pd`.  The last carrier equation
has two cases.  If `h=1`, then `p=w,d=w^-1` and `K=1`.  Otherwise
`h=p` is a nontrivial involution and `w=d=1`; its boundary is

```text
K=p_3p_2(p^-1u^-1)_0p^-1_1p_2u_0p_2.
```

It cannot land in copy 1 because the initial `p_3` cannot vanish, and it
cannot land in another copy because its unique `p^-1_1` cannot vanish.
Branch II forces
`H=1,c=z,p=z^-1,d=1` and has `K=1`.  Branch III has the same carrier split
as branch I: its `h=1` case has identity boundary, while its involutory case
has the same displayed residue and the same unique-syllable fence.

In branch IV, the first conjugacy equation has the same four maximal
noncrossing schemes as in the `0;142` proof.  They force

```text
g10=g11=g12=g13=1, xy=1, H=f_2.
```

The last carrier equation gives either `f=1` or a nontrivial involution
`f=p` with `a=1`.  The latter boundary is

```text
K=f^-1_3f^-1_2(f^-1u^-1)_0f^-1_1f_2u_0f_2,
```

which is not one-copy by its copy-3 and copy-1 syllables; the former is the
identity.  Branch V similarly forces `g3=1,H=f_2`.  Its exact cases are

```text
f=1, a=v, p=v^-1, K=1;
f=p!=1, f^2=1, a=1, v=1,
K=p_3p_2(p^-1u^-1)_0p^-1_1p_2u_0p_2.
```

For each of the last two involutory residues, the copy-1 syllable is unique.
A one-copy reduction would therefore have to land in copy 1, but its initial
nontrivial copy-3 syllable cannot then disappear.  This exhausts the class.
