---
rg: 2
id: positive-scaffold-has-quotient-compatible-rf-witness
kind: claim
title: The positive scaffold has a quotient-compatible residually finite benign witness
refuted_by: quotient-benign-witness-forces-finite-presentation
distinct_from:
  higman-half-row-has-regular-mf-benign-witness: that controls the operator-MF type of one base benign witness; this asks that the full recursive benign construction preserve a quotient map and residual finiteness through every closure operation.
  positive-rope-profinite-edge-synchronization: that is the resulting finite quotient family at the rope edge; this isolates the exact enhanced benign-witness data sufficient to construct it.
---

For the positive branch of the uniform FIN/INF scaffold, write its recursive
presentation as `Q=F/N`.  Construct, uniformly from the index, a benign
witness `(K,e,L)` for `N<=F` together with `sigma:K->Q` such that

```text
sigma e=q,                    L <= ker(sigma),                 (PCR1)
Q is effectively residually finite,                           (PCR2)
Gamma=<K,v | [v,L]=1> is effectively residually finite.        (PCR3)
```

Here effective residual finiteness means a computable sequence of finite
quotients in which each nonidentity element survives eventually.  No
retraction onto the rope edge is requested.  The target is to enhance the
benign-subgroup closure calculus so that the quotient map in `(PCR1)` and the
finite quotients in `(PCR2)`--`(PCR3)` survive its machine construction.

## Attempts

The active approach is to decorate every `BenignWitness` produced by the
Higman operation calculus with a map to the current quotient, then audit the
base cases and the nine closure operations for preservation of `(PCR1)`.
Ordinary benignness alone cannot recover that map: its data record only the
intersection `e(F) intersect L=e(N)`, and normal closure of `L` in `K` can
meet `e(F)` in more than `e(N)`.  Residual finiteness is a separate audit;
even a quotient-compatible witness does not imply `(PCR3)` without a
profinite-closedness condition on `L<=K`.

This attack is now closed more strongly.  If `(PCR1)` held, quotienting `K`
by the normal closure of the finitely generated `L` would produce a finitely
presented group containing `Q` as a retract.  Hence `Q` would be finitely
presented, contrary to the delayed positive branch.  This is established by
`quotient-benign-witness-forces-finite-presentation`.
