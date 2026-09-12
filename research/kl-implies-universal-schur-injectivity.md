---
rg: 2
id: kl-implies-universal-schur-injectivity
kind: claim
title: The Kervaire--Laudenbach conjecture for all groups implies universal Schur injectivity
distinct_from:
  universal-schur-injectivity-for-nonsingular-adjunctions: that is the universal injectivity statement itself; this is only the implication from coefficient injectivity for all groups to it, the converse of kl-failure-yields-a-schur-kill.
  kl-failure-yields-a-schur-kill: that proves a coefficient kill gives a Schur kill; this asks whether a Schur kill conversely forces some coefficient kill.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

**OPEN.** If `G -> (G * <t>)/<<w>>` is injective for every countable `G` and
every nonsingular `w`, then `H_2(Q) -> H_2((Q * <t>)/<<w>>)` is injective for
every countable `Q` and every nonsingular `w`.

## Attempts

1. **Central extension by `Q/Z`.** A killed class `x` is detected by some
   `gamma : H_2(Q) -> Q/Z`. By `central-extension-kl-schur-criterion`, the
   center of the realizing extension `E` dies in the **centralized** quotient
   `(E * <t>)/<<w, [Z, t]>>`, while the conjecture only controls the plain
   quotient `(E * <t>)/<<w>>`. The extra relators `[z, t]` have exponent sum
   zero. The augmented presentation `<t | t^m, 1>` has second homology `Z`, so
   the generalized conjecture does not predict solvability of the system either.
   This attempt dies at that gap.
2. **Reverse the torus amalgam.** `kl-failure-yields-a-schur-kill` produces
   only torus classes of killed coefficients. A general killed class, such as a
   Maslov class of `Sp_4(Z)`, need not be the image of any such torus, so the
   construction does not reverse.
