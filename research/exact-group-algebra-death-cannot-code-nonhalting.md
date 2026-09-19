---
rg: 2
id: exact-group-algebra-death-cannot-code-nonhalting
kind: claim
title: Exact group-algebra death cannot computably separate NONHALT from HALT
distinct_from:
  computable-regular-trace-fanizza-return-would-decide-halting: that derives literal death from one specific regular-trace Fanizza heat compiler; this is the recursion-theoretic no-go for every uniformly recursively presented group-algebra compiler.
  group-algebra-mark-reverse-kleene-collapse: that deliberately asks only for matrix-microstate norm collapse on NONHALT; this proves why replacing that semantic collapse by equality in the group algebra is impossible.
  canonical-profile-kleene-higman: that positively consumes qualitative canonical-profile collapse; this is a negative theorem about exact algebraic vanishing before any microstate argument.
---

**ESTABLISHED.**  There is no total computable compiler which sends every
Turing-machine index `e` to a finite alphabet `S_e`, a uniformly recursively
enumerable relator stream `R_e`, and a finite rational expression

```text
p_e=sum_j c_(e,j) w_(e,j) in Q[F(S_e)]
```

such that, for `Gamma_e=<S_e|R_e>`,

```text
e halts     => p_e!=0 in Q[Gamma_e],                    (EGD1)
e nonhalts  => p_e=0  in Q[Gamma_e].                    (EGD2)
```

Indeed, equality of a finite rational group-algebra expression to zero is
recursively enumerable, uniformly in a recursively enumerable presentation.
Thus `(EGD2)` and `(EGD1)` would make the zero set of the compiled marks
exactly `NONHALT`.  Both `HALT` and `NONHALT` would then be recursively
enumerable, deciding the halting problem.

The orientation matters.  The reverse-Kleene compiler may consistently ask
for

```text
e nonhalts => ||p_e(U_n)||_2->0
```

only along finite-dimensional canonical-profile microstates, while retaining
`p_e!=0` in the group algebra.  Such matrix-only collapse is not an equality
certificate and therefore does not enumerate `NONHALT`.  In fact, if a
compiler with that semantic property exists, the fixed-point construction
uses precisely the resulting mismatch between the faithful regular norm and
the microstate norm to prove nonhyperlinearity.

This no-go also corrects a tempting but invalid strengthening of
MIP-star/game groupification: NONHALT soundness cannot be compiled into
literal group-ring death while HALT completeness keeps the same mark alive.
The groupification must instead create a genuine qualitative approximation
collapse (or an equivalent canonical-trace obstruction).
