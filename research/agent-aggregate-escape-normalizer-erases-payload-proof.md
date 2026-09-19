---
rg: 2
id: agent-aggregate-escape-normalizer-erases-payload-proof
kind: route
title: Conjugate the full-support complement through the normalizer
target: agent-aggregate-escape-normalizer-erases-payload
requires:
  - agent-aggregate-escape-forbidden-support-saturation
---

Because `U A U^*=A` and `Q in A'`, the projection `R=UQU^*` belongs to
`A'`.  Also `D<=R`, so `Hull_A(D)<=R`.

Let

```text
T=R-Hull_A(D).
```

Then `T in A'`, `T<=R`, and `TD=0`.  Conjugating by `U^*` gives a reducing
projection

```text
T_0=U^*TU<=Q
```

for `A`, because `U` normalizes `A`.  Moreover

```text
0=U^*TDU=T_0QB_f=T_0B_f.                              (1)
```

Full reducing support of `B_f` on `Q` forces `T_0=0`; hence `T=0` and
`Hull_A(D)=R`.  Since both `Q` and `R` reduce `A`, their join reduces `A`,
so the smallest reducing projection containing `Q join D` is exactly
`Q join R`.  This proves `(ANP2)--(ANP3)`, and induction gives `(ANP4)`.

For a fixed approximate normalizer packet, exactify it first and conjugate
the corrected shared algebra exactly.  Apply `(AFS4)` to the reducing
complement `T` with the fixed-word transport error as `delta`.  Since
`delta=O(sqrt(E))`, the `delta^2` contribution is `O(E)` and the structural
gap contribution is `O(sqrt(E))`.  This proves the asserted perturbative
form.

