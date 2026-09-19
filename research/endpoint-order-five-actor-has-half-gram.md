---
rg: 2
id: endpoint-order-five-actor-has-half-gram
kind: claim
title: The odd endpoint actor forces a half Gram and a signed-sheet one-third Gram
artifacts:
  - research/endpoint-order-five-half-gram-proof.md
  - experiments/endpoint_fine_collision_odd_mixed_audit.py
distinct_from:
  endpoint-whitehead-hecke-flag-trichotomy: that classifies every endpoint placement and finds a flexible fine-only collision on the canonical signed sheet; this adjoins the native order-seven head and obtains a representation-independent half Gram on its four-root orbit before that sheet is imposed.
  native-whitehead-hecke-head-has-order-seven-anchor: that gives the native order-seven occurrence for each Hecke head; this couples the second head to the endpoint Whitehead and finds the new odd order-five relation.
  endpoint-detector-cell-retains-coboundary-gauge: that transports the endpoint detector through a reversible S3 profile with maximal Grams; this obtains a proper half Gram from a GL4 character orbit and then locates its exact signed-sheet attachment failure.
---

**ESTABLISHED RAW HALF-GRAM AND SIGNED-SHEET GRAM.**  Retain the unique
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

The words are supported on the literal four-projective-summand corner

```text
D=qE_55+e_2E_88+e_3E_99+e_3E_22.                      (OFG5)
```

On the first three summands `M` is the faithful native `GL_3(F_2)` Singer
matrix and on the fourth it is the identity.  The word `W` literally swaps
the second and fourth summands and fixes the other two.  Both words are the
identity on `1-D`.  Consequently, globally in the elementary group,

```text
<M,W>|V = GL_4(F_2),       |GL_4(F_2)|=20160,
W^2=M^7=(WM)^5=1.                                     (OFG6)
```

The action is transitive on the `15` nonzero characters of `V`.  Let `pi`
be any finite-dimensional unitary representation of this finite packet and
write

```text
R =1_(C_3=-1,s=+1),
R*=1_(C_3=-1,s=+1,s'=+1).                              (OFG7)
```

The condition `C_3=-1` excludes the zero character.  In the unique nonzero
orbit, `(OFG7)` selects respectively `4` and `2` characters.  Covariance
forces equal multiplicity on the orbit, so, in **every** representation,

```text
rank(R*)=(1/2)rank(R).                                  (OFG8)
```

Since `W` fixes `C_3` and swaps `s,s'`, the literal compressed endpoint word
satisfies

```text
(RWR)^*(RWR)=R*,       ||RWR||_2^2=(1/2)tau(R).        (OFG9)
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

The full half does not survive arbitrary conditioning, but a uniform third
does survive the prescribed center-chain sheet.  For

```text
K_1=<C_1,C_2,C_3,v,w>,
p_1=e_(K_1,lambda),                 p_2=p_1(1+s)/2,
```

the subgroup of the actor in `(OFG6)` which fixes the first projective
summand both as a vector and a covector is

```text
G_1={diag(1,B):B in GL_3(F_2)} ~=GL_3(F_2),
|G_1|=168.                                               (OFG10)
```

Every element of `G_1` fixes signed `K_1` pointwise.  Indeed `C_2,v` enter
the active block only through its first target summand, `C_3` leaves only
through its first source summand, `w` is disjoint, and the coordinate-`2`
support of `C_1` is `q`, orthogonal to the `e_3` summand moved by `G_1`.

The projection `p_1` therefore reduces the commuting complement

```text
U=<s,t,s'>~=C_2^3
```

and `G_1` acts as the full `GL_3(F_2)` on `U`.  Hence, inside `p_1`, the
zero `U`-character has some multiplicity `m_0` and each of the seven
nonzero characters has one common multiplicity `m_1`.  Since

```text
p_2=p_1 1_(s=+1),             p_*=p_2 1_(s'=+1),
```

the three ranks are

```text
rank(p_1)=m_0+7m_1,
rank(p_2)=m_0+3m_1,           rank(p_*)=m_0+m_1.       (OFG11)
```

Consequently, in every finite-dimensional representation,

```text
rank(p_2) >= (3/7)rank(p_1),
rank(p_*) >= (1/3)rank(p_2),
rank(p_*) >= (1/7)rank(p_1),
||(p_2Wp_2)||_2^2=tau(p_*) >= (1/3)tau(p_2).           (OFG12)
```

This is the first representation-independent positive Gram on the actual
signed fine flag.  It bypasses the earlier swapped-character zero-meet
profile by aggregating its compensating `G_1` sheets.  It is still an
analytic finite-sheet aggregation: it does not identify `W` with either
prescribed native unequal selector occurrence, and `p_*` is not asserted
to reduce `M`.  Thus `(WM)^5=1` does not yet remove the polar reservoir
factor on this cut.

The shortest endpoint detector compositions do not repair this typing:

```text
WA_2: x_83(b_2) |-> x_23(b_3)x_53(q),
A_2W: x_83(b_2) |-> x_23(b_3).                          (OFG13)
```

The additional `x_53(q)` is a noncentral, literal mark-saturated exit, but
it is outside the signed `K_1` return.  Isolating it by comparing the two
rows uses an even number of `W` occurrences and supplies no odd fixed-sheet
selector row.

Thus `(OFG12)` closes positivity of the endpoint Gram even after the literal
signed-sheet cut.  The remaining seam is occurrence typing: authenticate
this endpoint polar as the reservoir gauge of the actual coarse/fine native
selector rows.  The shortest endpoint returns in `(OFG13)` do not do so.

The four-bit enumeration is the exact conjugation action on the invariant
root group `V`; it is not a truncation of arbitrary Leavitt coefficients.
The word relations in `(OFG6)` were separately replayed with faithful sparse
Leavitt normal forms.  Reversing `(OFG2)` produces a different word and must
not be substituted.

No Property `(T)`, canonical trace, literature theorem, local computation,
or Lean compilation is used.

DERIVATION
endpoint-order-five-half-gram-proof
