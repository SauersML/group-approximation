---
rg: 2
id: forty-two-branch-gram-polar-rounding
kind: claim
title: One cross-overlap scalar rounds the forty-two branch candidates to a common partial PVM
distinct_from:
  polar-compression-turns-band-mismatch-into-first-exit: that polar-rounds one raw transition between two already-chosen band projections; this simultaneously orthogonalizes all branch projections and controls the resulting common-PVM covariance energy.
  arithmetic-global-pvm-does-not-bypass-coset-action-gate: that describes the residual finite-atomic enemy after a global lamp PVM has been decoded; this supplies only the finite-shell algebraic rounding step and makes no claim that a global PVM eliminates that enemy.
  a5-center-spectrum-has-constant-one-site-hamming-gap: that recovers a site permutation from the center of one complete finite simple packet but cannot complete partial sites; this rounds already-labelled branch projections by their total matrix Gram overlap, without using packet centers.
  bounded-cooccurrence-joint-pvms-do-not-round-globally: that refutes global rounding from bounded local jointness alone; this assumes and explicitly exposes the missing global cross-overlap scalar.
---

ESTABLISHED.  Let `I` be a finite label set (for the native shell,
`|I|=42`) and let `(P_i)_(i in I)` be projections in `M_d(C)` satisfying

```text
sum_i rank(P_i) <= d.                                    (FGP1)
```

Define the total ordered cross-overlap

```text
Omega=sum_(i!=j) tr_d(P_i P_j).                         (FGP2)
```

Then there are pairwise orthogonal projections `(E_i)_(i in I)` with
`rank(E_i)=rank(P_i)` such that

```text
sum_i ||E_i-P_i||_(2,d)^2 <=4 Omega.                    (FGP3)
```

Thus `(E_i)` is one exact partial PVM of the same total marked mass.  No
lower bound on individual branch ranks and no matrix-dimension-dependent
constant occurs.

The rounding also preserves finite-shell covariance quantitatively.  Suppose
a symmetric actor packet `S` permutes `I`, with raw unitaries `W_s`, and put

```text
E_raw=(1/|S|) sum_(s,i)
      ||W_s P_i W_s^*-P_(s.i)||_(2,d)^2.                (FGP4)
```

Then the rounded common PVM satisfies

```text
E_round=(1/|S|) sum_(s,i)
        ||W_s E_i W_s^*-E_(s.i)||_(2,d)^2
 <=3 E_raw+24 Omega.                                    (FGP5)
```

For the native `42`-branch shell, the sole remaining algebraic input is
therefore the scalar estimate

```text
Omega <= C (mixedRootEnergy + firstExitMass).            (FGP6)
```

Once `(FGP6)` is obtained from the six conductor/root packets, `(FGP3)`
produces the common same-basis partial PVM and `(FGP5)` turns the raw actor
words into its controlled transport energy.  Iterating the decoded shells
can then assemble the finite-support object consumed by the established
infinite Schreier PVM inequality.  Pairwise local
jointness cannot imply `(FGP6)` by itself, as the bounded-cooccurrence Pauli
countermodel shows; the mixed-root relations must control this global Gram
sum or charge it to first exits.
