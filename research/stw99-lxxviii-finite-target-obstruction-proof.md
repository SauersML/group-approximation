---
rg: 2
id: stw99-lxxviii-finite-target-obstruction-proof
kind: route
title: Lift one proper isometry from the sequence relative commutant
target: stw99-lxxviii-finite-target-obstruction
requires: []
---

If `phi` were `O_infinity`-stable, there would be a unital embedding

```text
O_infinity -> B_infinity cap phi(A)'.
```

In particular, `B_infinity` would contain an isometry `v` with nonzero defect
`1-vv*`.  Choose a bounded representing sequence `(v_n)` in `B`.  Then

```text
||v_n* v_n-1|| -> 0,
limsup_n ||1-v_n v_n*|| = 1.
```

Pass to a subsequence on which the second norm converges to one.  For all
large `n`, polar correction gives an isometry

```text
s_n=v_n(v_n*v_n)^(-1/2) in B,
```

with `||s_n-v_n||->0`.  Hence `s_n` is nonunitary for large `n`, contradicting
finiteness of `1_B`.  Thus `phi` is not `O_infinity`-stable.  The absence of
normalized quasitraces is used only to place the pair within the hypotheses
of Problem LXXVIII.
