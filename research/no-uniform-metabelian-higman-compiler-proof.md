---
rg: 2
id: no-uniform-metabelian-higman-compiler-proof
kind: route
title: Use the uniform promise word problem for finitely presented residually finite groups
target: no-uniform-metabelian-higman-compiler
requires: []
---

Assume such a compiler exists.  Given a Turing-machine index `e`, enumerate
the one-generator recursive presentation

```text
Q_e=<a | a if machine e halts>.
```

If the machine halts, enumerate the relator `a`; otherwise enumerate no
relator.  Thus `Q_e` is respectively `1` or `Z`, and in particular it is
abelian for every `e`.

Run the compiler and write `P_e=C(Q_e)` and
`u_e=iota_(Q_e)(a)`.  By the positive guarantee, `P_e` is a finitely
presented metabelian group.  Every finitely generated metabelian group is
residually finite (P. Hall), so the word problem in `P_e` can be solved
uniformly from its finite presentation under this promise.  On input a word
`u`, dovetail:

1. the enumeration of van Kampen derivations of `u=1`; and
2. the enumeration of finite multiplication tables and all assignments of
   the presentation generators which satisfy every relator, stopping when
   the image of `u` is nontrivial.

If `u=1`, process 1 stops.  If `u!=1`, residual finiteness supplies a finite
quotient separating it, so process 2 stops.  Hence exactly one answer is
eventually obtained.

Apply this algorithm to `u_e`.  Since `iota_(Q_e)` is injective,

```text
u_e=1 in P_e  iff  a=1 in Q_e  iff  machine e halts.
```

This decides the halting set, contradiction.  The same proof only uses
that all `Q_e` are abelian and all `P_e` are residually finite, giving the
stronger formulation in the claim.
