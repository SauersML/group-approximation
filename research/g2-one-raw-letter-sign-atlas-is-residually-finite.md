---
rg: 2
id: g2-one-raw-letter-sign-atlas-is-residually-finite
kind: claim
title: The long router plus either one raw Jacobson letter is residually finite
artifacts:
  - research/g2-one-raw-letter-sign-atlas-rf-proof.md
distinct_from:
  g2-conditioned-jacobson-sign-envelope-is-finite: that traps the Q/QT sign packet in an eight-element ring; this adds g_2 and one literal unmasked T or S occurrence at arbitrary word length.
  qutrit-one-raw-letter-head-router-is-residually-finite: that treats the full scalar group with q and one raw letter; this also treats the asymmetric S plus QT algebra needed by the sign packet.
  qutrit-two-branch-sign-polar-has-hidden-half-absorber: that computes both literal branches in one acyclic finite packet; this identifies the sharp g_2 threshold before both orientations occur together.
---

Keep

```text
q=1-ST,                  a=qT,
H=x_(c_2,c_1)(q),        A_0=x_(c_2,c_0)(a),
W=x_(c_2,c_3)(q),
G_(sigma,tau)=E(1+sigma A_0)(1+tau W)/4.               (GRA1)
```

Let `U=x_(c_1,c_0)(T)` and `V=x_(c_0,c_3)(S)`. Then the
two entire one-raw-letter groups

```text
Lambda_U=<C,g_2,H,A_0,W,U>,
Lambda_V=<C,g_2,H,A_0,W,V>                              (GRA2)
```

are residually finite. More precisely,

```text
Lambda_U <= GL_28(B_-),       B_-=F_2<q,T>,

Lambda_V <= GL_28(B_+),       B_+=F_2<S,q,a=qT>,        (GRA3)
```

and both coefficient algebras are residually finite. Thus `g_2` and the
raw letter may occur in the same word, in either order and at arbitrary
length, without leaving an exact finite-quotient approximation class.

The complete length-one sign-support atlas is

| raw compression | surviving signs | qutrit-cut polar rank |
|---|---|---|
| `G_(sigma,tau) U G_(sigma,tau)` | `sigma=+` | `5/72` at `(+,+)`, `1/16` at `(+,-)` |
| `G_(sigma,tau) V G_(sigma,tau)` | `tau=+` | `5/72` at `(+,+)`, `1/16` at `(-,+)` |

Every other row is zero. Left multiplication by any power of `g_2` is
unitary and leaves these source ranks unchanged. Hence the low-length
words `g_2U`, `Ug_2`, `g_2V`, `Vg_2` and all sign-masked versions
supply no new source rank beyond the established `5/72,1/16` table.

This is a full closure/no-go, not only a bounded enumeration. Since
`Lambda_U` and `Lambda_V` are finitely generated residually finite
groups, their canonical traces are limits of regular finite-quotient
traces. No normalized-Hilbert--Schmidt obstruction can be derived from
relations contained wholly in either group.

Therefore a Hall witness using the long router must expose **both**
orientations in its same support-preserving/target-forcing operator. One
raw `U` or one raw `V`, even with unrestricted `g_2` conditioning,
is exactly absorbed.
