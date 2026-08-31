---
rg: 2
id: first-g2-mixed-return-has-a-dihedral-half-absorber
kind: claim
title: The first g2-conditioned two-orientation return is cut by a dihedral sign
artifacts:
  - research/first-g2-mixed-return-dihedral-half-absorber-proof.md
distinct_from:
  g2-one-raw-letter-sign-atlas-is-residually-finite: that treats either raw orientation at arbitrary word length; this is the first collected return containing g_2 and both raw orientations.
  g2-conditioned-jacobson-sign-envelope-is-finite: that contains only q and qT; this exposes ST=1-q before proving that the collected return falls back into a finite envelope.
  qutrit-mixed-orientation-head-return-is-quarter-polar: that uses TS=1 on an acyclic chain; this uses the opposite product ST=1-q and computes the new sign-cut polar rank.
---

Retain

```text
q=1-ST,                 a=qT,                  p=ST=1-q,
H=x_(c_2,c_1)(q),       A=x_(c_2,c_0)(a),
W=x_(c_2,c_3)(q),
G_(sigma,tau)=E(1+sigma A)(1+tau W)/4,
E=(1-H)/2.                                             (GMR1)
```

Let `U=x_(c_1,c_0)(T)`, `V=x_(c_0,c_3)(S)`, and use the
first four entries `c_0,c_1,c_2,c_3` of the long cycle `g_2`. Then

```text
U_2=g_2^2 U g_2^(-2)=x_(c_3,c_2)(T),
P=[V,U_2]=x_(c_0,c_2)(ST)=x_(c_0,c_2)(p).              (GMR2)
```

Thus `(GMR2)` is the first forward `g_2`-conditioned two-raw-letter
return which sees `ST` rather than `TS`. It contains both raw orientations
in the same word, but Steinberg collection removes them and leaves the
complementary head coefficient `p=1-q`.

The opposite head-sign root `A` detects a new involution:

```text
Z=[P,A]=(PA)^2=I+aE_(c_2,c_2),
<P,A> isomorphic to D_8.                               (GMR3)
```

Moreover `Z` commutes with `H,A,W`. For every sign pair,

```text
(G_(sigma,tau) P G_(sigma,tau))^2
 =G_(sigma,tau)(1+Z)/2.                                (GMR4)
```

Consequently the polar support is not the original sign carrier. It is
the carrier cut by the hidden dihedral sign `Z=+1`.

This loss persists after the qutrit source cut `R=e_0+e_1`. In the
canonical group trace the exact ranks are

| `(sigma,tau)` | `tau(supp abs(G_(sigma,tau)PG_(sigma,tau)R))` |
|---|---:|
| `(+,+)` | `43/1152` |
| `(+,-)` | `7/192` |
| `(-,+)` | `7/192` |
| `(-,-)` | `7/192` |

Every entry is strictly below the proposed target capacity:

```text
43/1152 < 1/18,                 7/192 < 1/18.           (GMR5)
```

There is an exact finite absorber for this collected return. The group

```text
F=<C,H,A,W,P>
```

has order `18432` and lies over the eight-element coefficient algebra

```text
D=span_(F_2){1,q,a},      q^2=q, qa=a, aq=a^2=0.        (GMR6)
```

Its regular representation retains every element in `(GMR1)--(GMR4)`
and realizes the displayed ranks exactly. Hence the shortest
`ST`-exposing return gives no Hall deficit.

This is a firewall for the **collected return**, not a claim that
`<C,g_2,U,V>` is finite or residually finite. A surviving word must keep
an uncancelled raw `S` or `T` coefficient and an uncancelled `g_2` target
leg after collection. Merely inserting both raw letters inside a
commutator which reduces to `P` is completely absorbed.
