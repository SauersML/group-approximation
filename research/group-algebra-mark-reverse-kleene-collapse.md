---
rg: 2
id: group-algebra-mark-reverse-kleene-collapse
kind: claim
title: Reverse Kleene diagonalization accepts a finite group-algebra mark
distinct_from:
  kleene-halting-mark-collapse-diagonal: that uses a marked group word and a fixed separation threshold; this uses a rational group-algebra element and only asymptotic norm collapse.
  trace-conditioned-reverse-kleene-collapse: that permits canonical moment side tests for a group-word mark; these side tests remain available here.
---

Suppose a total computable compiler sends each Turing-machine index `e` to a
finite presentation

```text
Gamma_e=<S_e|R_e>
```

and a finite rational group-algebra expression

```text
p_e=sum_j c_(e,j) w_(e,j) in Q[Gamma_e].              (GAK1)
```

Assume:

```text
machine e halts  =>  p_e != 0 in Q[Gamma_e],          (GAK2)
```

and, whenever `e` does not halt, every sequence of finite-dimensional unitary
tuples `U_n` whose relator defects tend to zero and whose finitely many
specified trace moments tend to their canonical values satisfies

```text
||p_e(U_n)||_2 -> 0.                                  (GAK3)
```

Then one can effectively specify a finitely presented nonhyperlinear group.

The mark may in particular be an algebraic projection in a selected finite
group type corner, such as

```text
p_e=q_rho D_e,
```

where `q_rho` is a rational central idempotent of a finite subgroup.  No
single group word has to isolate that type, and no uniform positive lower
bound on its canonical trace has to be computed.

This removes the **mark return** obstruction from selected signed-Hecke
corners.  It does not make a router preserve the selected corner or supply a
compatible projection atlas; those remain representation-theoretic inputs to
`(GAK3)`.

