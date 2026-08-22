---
rg: 2
id: leavitt-d4-l14-n0511-branch-i-needs-nontrivial-carrier
kind: claim
title: The normal six-winner branch I is fenced unless its two-copy carrier is nontrivial
distinct_from:
  leavitt-d4-l14-six-winner-profile-has-two-classes: that classifies and exposes the two new carrier systems; this performs the first exact nonabelian elimination in the normal 0;511 system.
  leavitt-d4-l14-rank9-n0115-is-fenced: that eliminates five branches in the first length-fourteen profile; this treats the different composite seven-syllable word in the second profile.
  paired-same-reservoir-boundary-lemma: that asks for normalized-HS authentication of a physical Leavitt carrier; this is a coefficient free-product reduction and isolates the exact algebraic carrier that would have to survive before any HS argument begins.
---

# The normal six-winner branch I is fenced unless its two-copy carrier is nontrivial

**ESTABLISHED.**  In the normal `0;511` class of the profile
`---++-+-++++++`, set

```text
a=g1, b=g2, c=g4, d=g5, e=g6, f=g7, g=g8,
t=g9, i=g10, j=g11, k=g12, l=g13,
q=bc,                 r=la.                             (N51-1)
```

After the common equation has forced `g0=g3=1`, the relevant coefficient
words are

```text
H  =k_1 r_2 q_1 d_2 e_1 f_2 g_1 t_2,
A0 =a_3 q_2 d_3 e_2 f_3 g_2 t_3,
C1 =k_0 r_1 b_0,
E1=q_3, E2=d_0, E3=e_3, E4=f_0, E5=g_3,
E6=t_0 i_1 j_2 k_3,   E7=r_0.                          (N51-2)
```

The first carrier equation is

```text
H A0=E7^-1 H.
```

Hence `H A0 H^-1=r_0^-1`.  The left side lies in the free product of
copies `1,2,3`, while the right side lies in copy `0`.  Their intersection
is trivial, so

```text
r=1,                 A0=1.                              (N51-3)
```

The alternating seven-syllable equation `A0=1` has the same five maximal
noncrossing branches as the length-fourteen splitter.  In branch I it reads

```text
q=e=g=1,             a d f t=1.                         (N51-4)
```

Projecting the remaining carrier equation to copies zero and three gives

```text
k b=f^-1d^-1=t a,      q e g=1.                         (N51-5)
```

In branch I the full remaining carrier equation reduces identically to
`(N51-5)`; its only unresolved carrier is

```text
H=k_1 a^-1_2.                                           (N51-6)
```

If this carrier is trivial, free-product normal form gives `k=a=1`, hence
`l=1`, `b=t`, and `c=t^-1`.  The boundary becomes

```text
i_0 j_1 t^-1_0 i_2 j_3 t_0 i_1 j_2.                   (N51-7)
```

If `i=j=1`, `(N51-7)` is the identity.  Otherwise it is a reduced word in
at least three coefficient copies: setting only `i`, only `j`, or only `t`
to one leaves alternating copy indices, and the only possible same-copy
merge (`i_0t^-1_0` when `j=1`) still leaves copies `2` and `1`.  Thus it is
never a nontrivial one-copy boundary.

Consequently every branch-I counterexample in this fresh profile must keep
the genuinely nontrivial two-copy carrier `k_1a^-1_2`.  The scalar-carrier,
stationary-support, and trivial-holonomy subbranch is algebraically fenced;
same-carrier HS authentication cannot rescue it.  The cases `H!=1` and the
other four splitter branches remain open.

