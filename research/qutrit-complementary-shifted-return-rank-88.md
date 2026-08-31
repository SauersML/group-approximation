---
rg: 2
id: qutrit-complementary-shifted-return-rank-88
kind: claim
title: The complementary shifted Leavitt return has rank 88 and cannot repair the first half-loss
artifacts:
  - experiments/qutrit_complementary_shifted_return_rank.py
  - research/qutrit-complementary-shifted-return-rank-proof.md
distinct_from:
  fixed-g2-mixed-pair-has-all-length-d8-normal-form: that exhausts arbitrary words in the branch-zero shifted S/T pair; this tests the genuinely different branch-one return s1 t1=q.
  qutrit-two-branch-sign-polar-has-hidden-half-absorber: that treats the two literal branches before the long g2 shift; this computes the first g2-shifted occurrence of the complementary branch.
  first-g2-mixed-return-has-a-dihedral-half-absorber: that computes the branch-zero shifted return s0 t0=1-q with (+,+) rank 344 on the active regular block; this computes the q return and combines the two source capacities.
---

Keep the qutrit/Jacobson sign packet

```text
q=s_1t_1=1-s_0t_0,             a=qt_0,
H=x_(c_2,c_1)(q),
A=x_(c_2,c_0)(a),
W=x_(c_2,c_3)(q),
G_(sigma,tau)=E(1+sigma A)(1+tau W)/4.
```

The first shifted mixed return uses branch zero and has coefficient
`s_0t_0=1-q`.  Apply the identical coordinate placement to branch one:

```text
V_1=x_(c_0,c_3)(s_1),
U_(1,2)=g_2^2 x_(c_1,c_0)(t_1) g_2^(-2)
       =x_(c_3,c_2)(t_1).
```

Then the Steinberg relation gives the complementary returned root

```text
P_q=[V_1,U_(1,2)]=x_(c_0,c_2)(s_1t_1)
   =x_(c_0,c_2)(q).                                     (QCR1)
```

The active subgroup

```text
F_q=<k,H,A,W,P_q>
```

is finite of order `6144`.  On its regular module, after selecting the same
nontrivial `k` character used by the qutrit source, the exact ranks of

```text
G_(sigma,tau) P_q G_(sigma,tau) e_k
```

are

```text
(+,+): 88,
(-,+): 84,
(+,-): 84,
(-,-): 84.                                               (QCR2)
```

The calculation is exact over `Q(omega)`, `omega^2+omega+1=0`.  It uses the
faithful eight-element coefficient algebra

```text
D=F_2 1 direct-sum F_2 q direct-sum F_2 a,
q^2=q, qa=a, aq=a^2=0,
```

and exact sparse Gaussian elimination; there is no floating-point or
finite-field rank inference.

The qutrit source chooses two of the three central `h` characters.  Hence the
normalized polar-source ranks are

```text
(+,+): 2*88/(3*6144)=11/1152,
others: 2*84/(3*6144)=7/768.                             (QCR3)
```

This is much smaller than the first branch-zero shifted source
`43/1152` from `first-g2-mixed-return-has-a-dihedral-half-absorber`.  More
strongly, any linear interference operator whose initial space is contained
in the sum of the two shifted polar-source spaces satisfies

```text
rank_source <= (43+11)/1152 = 3/64
            < 1/18,                                     (QCR4)
```

where `1/18` is the target `Ee_2` capacity.  The containment is automatic
for any linear combination of the two compressed returns because
`ran((X_0+X_1)^*)` is contained in `ran(X_0^*)+ran(X_1^*)`.

Therefore the missing carrier cannot be repaired by using both Leavitt
branches in the same shifted coordinate cell, even with arbitrary scalar
interference between those two compressed returns.  The next viable mixed
word needs a second inequivalent raw **placement** whose source support is
not contained in this two-return span, or a genuinely new joint relation.

**ESTABLISHED 2026-08-31** by
[[qutrit-complementary-shifted-return-rank-proof]].
