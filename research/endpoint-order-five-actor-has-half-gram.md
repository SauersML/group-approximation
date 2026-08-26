---
rg: 2
id: endpoint-order-five-actor-has-half-gram
kind: claim
title: The odd endpoint actor forces a half Gram before the signed K1 sheet
artifacts:
  - research/endpoint-order-five-half-gram-proof.md
  - experiments/endpoint_fine_collision_odd_mixed_audit.py
distinct_from:
  endpoint-whitehead-hecke-flag-trichotomy: that classifies every endpoint placement and finds a flexible fine-only collision on the canonical signed sheet; this adjoins the native order-seven head and obtains a representation-independent half Gram on its four-root orbit before that sheet is imposed.
  native-whitehead-hecke-head-has-order-seven-anchor: that gives the native order-seven occurrence for each Hecke head; this couples the second head to the endpoint Whitehead and finds the new odd order-five relation.
  endpoint-detector-cell-retains-coboundary-gauge: that transports the endpoint detector through a reversible S3 profile with maximal Grams; this obtains a proper half Gram from a GL4 character orbit and then locates its exact signed-sheet attachment failure.
---

**ESTABLISHED RAW HALF-GRAM WITH A SHARP SHEET FENCE.**  Retain the unique
fine collision

```text
W=What_(8,2;2),             s=x_68(a_2),
s'=WsW=x_62(a_3),           C_3=x_65(q),              (OFG1)
```

and the second native order-seven head

```text
M=J_2B_3A_2,                M^7=1.
```

Here the native orientation is essential:

```text
J_2=x_98(c_2)x_89(d_2)x_98(c_2)=What_(8,9;2).          (OFG2)
```

Put `t=x_69(a_3)`.  The four row-six roots commute and are independent:

```text
V=<C_3,s,t,s'> ~= C_2^4.                               (OFG3)
```

Exact Steinberg conjugation gives

```text
M: C_3 |-> C_3t,   s |-> t,   t |-> C_3s,   s' |-> s',
W: C_3 |-> C_3,    s |-> s',  t |-> t,      s' |-> s. (OFG4)
```

Consequently

```text
<M,W>|V = GL_4(F_2),       |GL_4(F_2)|=20160,
W^2=M^7=(WM)^5=1.                                     (OFG5)
```

The action is transitive on the `15` nonzero characters of `V`.  Let `pi`
be any finite-dimensional unitary representation of this finite packet and
write

```text
R =1_(C_3=-1,s=+1),
R*=1_(C_3=-1,s=+1,s'=+1).                              (OFG6)
```

The condition `C_3=-1` excludes the zero character.  In the unique nonzero
orbit, `(OFG6)` selects respectively `4` and `2` characters.  Covariance
forces equal multiplicity on the orbit, so, in **every** representation,

```text
rank(R*)=(1/2)rank(R).                                  (OFG7)
```

Since `W` fixes `C_3` and swaps `s,s'`, the literal compressed endpoint word
satisfies

```text
(RWR)^*(RWR)=R*,       ||RWR||_2^2=(1/2)tau(R).        (OFG8)
```

This is a genuine arbitrary-profile, nonmaximal cross Gram.  It is not a
canonical-trace calculation and it rules out the old two-character
zero-meet model on the unconditioned `V` carrier.  The order-five relation
is also a genuine odd occurrence anchor: a multiplicity involution `D`
commuting with this packet would give

```text
((WD)M)^5=D,
```

so the exact relator detects `D` dimension-independently on any common
reducing occurrence.

The prescribed center-chain sheet is not such an occurrence.  For

```text
K_1=<C_1,C_2,C_3,v,w>,
p_1=e_(K_1,lambda),                 p_2=p_1(1+s)/2,
```

one has the exact exits

```text
M C_2 M^(-1)=C_2 x_84(b_2),
M v M^(-1)=v x_87(x_1).                                  (OFG9)
```

Thus no nonzero power of `M` normalizes signed `K_1`.  More sharply, among
the `20160` actors in `(OFG5)`, exactly eight fix `C_3,s` and shear

```text
s' |-> C_3s'.                                            (OFG10)
```

Such a shear would exchange the two `s'` signs under `C_3=-1` and descend
the half split to `p_2`.  All eight exact lifted words fail to normalize
signed `K_1`; multiplying them by `K_1` cannot repair normalization.  Hence
the present finite actor proves `(OFG7)` only before conditioning on the
`C_2,v` sheet.  It does not prove a lower bound for `p_2Wp_2`.

The shortest endpoint detector compositions do not repair this typing:

```text
WA_2: x_83(b_2) |-> x_23(b_3)x_53(q),
A_2W: x_83(b_2) |-> x_23(b_3).                          (OFG11)
```

The additional `x_53(q)` is a noncentral, literal mark-saturated exit, but
it is outside the signed `K_1` return.  Isolating it by comparing the two
rows uses an even number of `W` occurrences and supplies no odd fixed-sheet
selector row.

Thus `(OFG7)--(OFG8)` are real progress: the endpoint/head packet itself
has the desired representation-independent proper Gram.  The remaining
seam is now exactly to aggregate or return the compensating `K_1` sheets
without destroying that half Gram.  Another power of the order-seven head,
a `K_1` dressing, or the two shortest endpoint returns cannot do it.

The four-bit enumeration is the exact conjugation action on the invariant
root group `V`; it is not a truncation of arbitrary Leavitt coefficients.
The word relations in `(OFG5)` were separately replayed with faithful sparse
Leavitt normal forms.  Reversing `(OFG2)` produces a different word and must
not be substituted.

No Property `(T)`, canonical trace, literature theorem, local computation,
or Lean compilation is used.

DERIVATION
endpoint-order-five-half-gram-proof
