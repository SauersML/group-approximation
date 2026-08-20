---
rg: 2
id: three-xor-violation-is-one-clifford-rank
kind: claim
title: A failed three-XOR equation is the minimal one-bit Clifford rank jump
artifacts:
  - experiments/taller_vidick_three_xor_rank_gate.py
distinct_from:
  boolean-predicate-is-one-rank-jump: that compiles an arbitrary truth table by an algebraic branching program; this uses the affine violation bit of a three-XOR equation and needs only a two-by-two diagonal pencil.
  support-failure-has-fixed-pivot-rank-one-compiler: that detects one nested-support atom; this uniformly handles either right-hand side of every three-XOR equation.
---

Write a three-XOR equation as

```text
x_1+x_2+x_3=b  over F_2
```

and put `v_b(x)=b+x_1+x_2+x_3`, so `v_b=1` exactly on a violation.  The affine
matrix

```text
M_b(x)=diag(1,v_b(x))
```

satisfies

```text
rank_F2 M_b(x)=1+v_b(x).                                 (TXR1)
```

Its class-two two-group packet has two commuting Pauli pairs with

```text
[p_1,q_1]=J,
[p_2,q_2]=J^b z_1 z_2 z_3,
```

and all cross commutators trivial.  In the sector `J=-1` and
`z_i=(-1)^x_i`, the irreducible packet dimension is `2` on a satisfying
assignment and `4` on a violation.  Restriction to the first Pauli pair is
respectively one or two copies of its unique two-dimensional spin type.

The lift is exact for every contextwise commuting selector tuple.  On a
four-dimensional ancillary factor take the first Pauli pair unconditionally;
take `p_2=X` and let `q_2` be `I` on satisfying joint spectral atoms and `Z`
on violating atoms.  Consequently the noisy three-XOR checks need not be
imposed as scalar equations: every assignment survives, while failure becomes
one discrete relative multiplicity bit.
