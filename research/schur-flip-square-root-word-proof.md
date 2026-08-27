---
rg: 2
id: schur-flip-square-root-word-proof
kind: route
title: Cancel the two packet implementers inside their commuting flip square
target: schur-flip-square-exposes-payload-root-word
requires: []
---

The two flips fix the selector center.  They multiply both factors of
`P_aQ_a` by `K`, so their product fixes that word:

```text
(alpha_P alpha_Q)(P_aQ_a)=K^2 P_aQ_a=P_aQ_a.
```

Thus `uv` commutes with `P_aQ_a`.  Since `u,v` are commuting involutions,

```text
d_a^2=(P_aQ_a)^2=[P_a,Q_a].
```

Multiplying by `A_a` and using `(SFR1)` proves `(SFR4)`.  Every factor in
`d_a` fixes the selector center, proving preservation of `A_a` and `(SFR6)`.

On a forbidden simple, the standard implementers of the two packet flips
are `Q_a` and `P_a`.  Schur's lemma therefore gives the displayed tensor
forms for `u,v`.  Direct multiplication yields

```text
P_aQ_a(Q_a tensor U_0)(P_a tensor V_0)=1 tensor U_0V_0,
```

which proves `(SFR5)`.  The relation `[u,v]=1` is equivalent on this block
to cancellation of the packet anticommutation by the opposite external
anticommutation.  This also shows why the construction is payload-tied.

