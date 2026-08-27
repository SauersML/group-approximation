---
rg: 2
id: augmentation-actor-semidir-is-not-fp
kind: claim
title: The canonical aperiodic augmentation semidirect product is not finitely presented
distinct_from:
  simple-t-augmentation-module-is-aperiodic: that proves the actor and character dynamics are ideal; this identifies the exact finite-presentation failure of the resulting group.
  compression-wreath-not-finitely-presented: that treats a particular compression wreath through a double-coset obstruction; this is the regular binary augmentation instance and uses a finite-index reduction.
---

Let `A` be any infinite finitely generated group and let

```text
W=F_2^(A) semidirect A = C_2 wr A,
Gamma_0=I_A semidirect A.                                (ASA1)
```

The augmentation ideal `I_A` has index two in the regular lamp module, so
`Gamma_0` has index two in `W`.  Restricted wreath products `C_2 wr A` with
nontrivial finite lamp and infinite acting group are not finitely presented
(the classical Baumslag finite-presentation obstruction).  Finite
presentability is invariant under passage to finite-index subgroups and
overgroups.  Therefore `Gamma_0` is not finitely presented.

This blocks the most canonical infinite-character actor despite its perfect
spectral dynamics.  The obstruction is the unbounded family of lamp-pair
commutators: diagonal translation leaves infinitely many pair-difference
orbits.  A successful finite presentation must compress those commutators
by an additional self-similar/oligomorphic mechanism **without** introducing
finite seed-visible character orbits or destroying the actor spectral gap.

Thus the infinite reformulation does not solve
`bounded-template-expanding-character-actor-family`; it replaces the finite
field tower by one sharply stated collision:

```text
aperiodic property-(T) character action
       + finitely presented abelian occurrence module.         (ASA2)
```
