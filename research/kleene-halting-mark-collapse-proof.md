---
rg: 2
id: kleene-halting-mark-collapse-proof
kind: route
title: Enumerate a van Kampen proof of triviality and diagonalize its halting behavior
target: kleene-halting-mark-collapse-diagonal
requires:
  - word-problem-of-finite-presentation-is-re
artifacts:
  - research/artifacts/fanizza-native-signal-diagonal-2026-08-20.md
---

For an index `e`, compute `(Gamma_e,w_e)` and let `N_e` enumerate all finite
van Kampen consequences of `R_e`, halting exactly when it finds a proof of
`w_e=1`.  Kleene's recursion theorem effectively supplies an index `e_*`
whose machine has the same behavior as `N_(e_*)`.

If `e_*` halted, its enumeration would prove `w_(e_*)=1`.  But `(KHC2)` would
apply to that same halting machine and give `w_(e_*)!=1`, a contradiction.
Thus `e_*` does not halt.  Completeness of the van Kampen enumeration also
shows directly that

```text
w_(e_*)!=1 in Gamma_(e_*).                                      (KHC4)
```

Now `(KHC3)` applies.  If `Gamma_(e_*)` were hyperlinear, microstates for its
canonical trace would have relator defect tending to zero and, by `(KHC4)`,

```text
||w_(e_*)(U_n)-I||_2^2 -> 2.
```

Eventually their defects are below `delta_(e_*)` and their marked distances
are strictly above `alpha_(e_*)`, contradicting `(KHC3)`.  Therefore the
effectively obtained finite presentation `Gamma_(e_*)` is nonhyperlinear.
