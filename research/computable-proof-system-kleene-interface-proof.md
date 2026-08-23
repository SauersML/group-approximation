---
rg: 2
id: computable-proof-system-kleene-interface-proof
kind: route
title: Gödel-code c.e. proof search and apply Kleene's recursion theorem
target: computable-proof-system-kleene-interface
requires: []
---

Fix a standard acceptable numbering `(varphi_e)` of partial computable
functions and a primitive-recursive coding of finite strings, finite
derivations, and formulas.  A computably axiomatized proof system is represented
by a c.e. set of valid derivation codes; dovetailing the axiom and rule
enumerators therefore gives a total computable enumeration of all proved
formula codes.

The fixed finite presentation and the already computable word family `e |->
r_e` make

```text
e |-> code("r_e != 1")
```

a total computable map of indices to formula codes.  Thus, uniformly in an
index for the proof enumerator and in `e`, there is a partial computable
program `P(e)` which enumerates proofs and halts exactly when it encounters a
proof whose conclusion is the formula `r_e != 1`.  The restricted soundness
hypothesis is simply the semantic implication

```text
P(e) halts  =>  r_e != 1
```

for this computable family of formulas; no soundness for unrelated formulas is
used.

By the parameter theorem (`s`-`m`-`n`), the code of `P(e)` is a total
computable function of `e`.  Kleene's second recursion theorem applied to that
function produces an index `e_T` whose program has exactly the behavior of
`P(e_T)`.  Equivalently, the resulting proof-search program can use the
numeral for its own index when forming the sentence it searches for.  This
packages the c.e. proof relation, the word-inequality syntax, restricted
soundness interface, and the required effective self-reference with no
additional group-theoretic assumption.
