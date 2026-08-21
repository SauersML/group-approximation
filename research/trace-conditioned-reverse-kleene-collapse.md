---
rg: 2
id: trace-conditioned-reverse-kleene-collapse
kind: claim
title: Reverse-Kleene collapse only needs soundness on canonical-trace profiles
distinct_from:
  kleene-halting-mark-collapse-diagonal: that assumes collapse for every sufficiently accurate finite-dimensional tuple; this permits finitely many strict moment side conditions which canonical-trace microstates satisfy.
  trace-conditioned-dimension-matched-kleene-diagonal: that diagonalizes against a search for a finite-dimensional witness and has the opposite HALT/NONHALT orientation; this retains the proof-enumeration reverse diagonal.
---

Suppose a total computable compiler sends each Turing-machine index `e` to

```text
(Gamma_e=<S_e|R_e>, w_e, delta_e, alpha_e,
 (t_(e,i),c_(e,i),eta_(e,i))_(1<=i<=r_e)),              (TCR1)
```

where `delta_e,eta_(e,i)>0`, `alpha_e<sqrt(2)`, the `t_(e,i)` are words,
and all displayed data are computable.  Assume

```text
machine e halts  =>  w_e != 1 in Gamma_e,                (TCR2)
```

and, if `e` does not halt, then

```text
tau_(Gamma_e)(t_(e,i))=c_(e,i) for every i,              (TCR3)
```

and every finite-dimensional unitary tuple `U` satisfying

```text
Def_(R_e)(U)<delta_e,
|tr(t_(e,i)(U))-c_(e,i)|<eta_(e,i) for every i            (TCR4)
```

also satisfies

```text
||w_e(U)-I||_2 <= alpha_e.                               (TCR5)
```

Then one can effectively specify a finitely presented nonhyperlinear group.

Thus a reverse-Kleene groupification theorem may be proved only on finite
tuples having a prescribed finite canonical-trace profile.  In particular,
one may require a fixed finite subgroup packet to be near its regular
character.  This does not by itself force a router to preserve a chosen
isotypic block; that remains a separate representation-theoretic decoder.
