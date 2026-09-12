---
rg: 2
id: maximal-sparse-character-atom-does-not-return-multiplicity
kind: claim
title: Coordinatewise maximal sparse character atoms do not close the Leavitt multiplicity recurrence
distinct_from:
  norm-corona-sparse-global-character-atom: that constructs one nonzero global character projection; this audits the attempted maximization of its coordinate ranks.
  leavitt-character-mass-escapes-to-finer-characters: that gives the general finite-window marginal obstruction; this isolates the stronger operator-norm proposal of choosing a maximal exact atom at every coordinate.
artifacts:
  - research/property-t-free-leavitt-full-mf-radical.md
---

**ESTABLISHED AUDIT.**  Start with the global sparse atom

```text
P=[P_n],                 rho(a)P=chi(a)P
```

from `norm-corona-sparse-global-character-atom`.  The branch conjugator and
the transverse shear produce, in the corona, `p` orthogonal copies of `P`
inside one global `F chi` character sector.  It is tempting to choose each
`P_n` to have maximal rank among the exact joint-character atoms of an exact
commuting torsion lift and then contradict maximality.

That comparison is invalid.  The returned projection `Q=[Q_n]` is a global
`F chi` atom only modulo `directSum M_(d_n)`: for every **fixed** coefficient
`a`, the wrong `rho(a)`-spectral part of `Q_n` tends to zero.  There is no
uniform statement over all coefficients at coordinate `n`.  Relative to the
chosen exact commuting lift, `Q_n` may therefore split among arbitrarily many
joint characters which agree with `F chi` on a growing finite window.  Each
exact atom can have rank at most `rank(P_n)` even though

```text
rank(Q_n)=p rank(P_n).
```

Thus maximality of a coordinate atom does not bound the rank of the returned
**corona** atom.  Passing to a subsequence so that the selected characters
converge pointwise constructs the global character but does not make the
conjugacy identities uniform on the moving coordinates.

Closing the argument would require a finite window which is simultaneously
branch invariant and retains the transverse character.  The former erases
the latter by `finite-branch-closure-erases-transverse-character`.  Hence the
maximal-atom proposal is another form of the same-reservoir return problem,
not a proof of it.

