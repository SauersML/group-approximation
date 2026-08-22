---
rg: 2
id: computable-regular-trace-fanizza-return-would-decide-halting
kind: claim
title: A computable regular-trace Fanizza return would decide the halting problem
distinct_from:
  universal-block-return-violates-the-regular-firewall: that rules out a functorial block return by applying it in one regular finite von Neumann algebra; this uses recursive enumerability of group-algebra zero to rule out the whole machine-indexed regular-trace compiler.
  group-algebra-mark-reverse-kleene-collapse: that permits semantic collapse only on canonical matrix microstates; this proves why replacing that collapse by literal group-algebra death is too strong.
  canonical-moments-linearize-fixed-depth-fanizza-return: that validly turns one regular trace inequality into one fixed-depth matrix estimate; this proves that demanding those inequalities at every depth cannot be the compiler.
---

**ESTABLISHED.**  No total computable compiler can satisfy
`(RHC1)--(RHC2)` of
`fanizza-regular-trace-heat-domination-compiler`.

## Proof

Assume such a compiler exists.  On a NONHALT instance, apply `(RHC2)` in the
left regular representation.  The Fanizza heat estimate gives

```text
0<=tau_(Gamma_m)(A_(m,t))<=C_m/(4t^2).                (CRF1)
```

Therefore

```text
0<=tau_(Gamma_m)(P_m^*P_m)<=C_m/(4t^2)               (CRF2)
```

for every `t`.  Sending `t->infinity` gives
`tau(P_m^*P_m)=0`.  Faithfulness of the canonical trace on the reduced group
C-star algebra implies

```text
P_m=0 in Q[Gamma_m].                                  (CRF3)
```

On a HALT instance, `(RHC1)` gives an exact representation in which `P_m`
is nonzero, so

```text
P_m!=0 in Q[Gamma_m].                                 (CRF4)
```

It remains to note that `(CRF3)` is recursively enumerable uniformly in
`m`.  Write the finite rational expression as

```text
P_m=sum_(j=1)^s c_j w_j.                              (CRF5)
```

Enumerate word-equality proofs from the recursively enumerable presentation.
In parallel enumerate partitions of `{1,...,s}` whose coefficient sum is
zero on every block.  Accept when, for one such partition, the equality
enumerator has proved all words within every block equal.  If this procedure
accepts, `(CRF5)` is zero.  Conversely, if `(CRF5)` is zero in the group
algebra, partition the support by equality in `Gamma_m`; every class has
coefficient sum zero and finitely many equality proofs eventually appear,
so the procedure accepts.

Thus `(RHC3)` would enumerate NONHALT, while ordinary simulation enumerates
HALT.  Running both procedures decides the halting problem, a contradiction.

The conclusion is sharp for the present route.  Fixed-depth regular trace
domination is a valid sufficient estimate one depth at a time, but a
computable family covering every depth converts semantic nonhyperlinearity
into literal algebraic death.  The successful return must hold only in
finite-dimensional canonical microstates and fail in the regular
representation; the matrix-only firewall is logically indispensable.

