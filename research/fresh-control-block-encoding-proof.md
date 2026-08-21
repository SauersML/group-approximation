---
rg: 2
id: fresh-control-block-encoding-proof
kind: route
title: Encode the acceptance product and isolate the surviving corner moments
target: block-encoded-acceptance-still-needs-corner-return
requires: []
---

Write `Q_j=I-L_j`, `R_j=I-2L_j`.  On a fresh control qubit define

```text
B_j=H_j(|0><0| tensor I+|1><1| tensor R_j)H_j
   =[[Q_j,L_j],[L_j,Q_j]].
```

Let `P=|0^m><0^m| tensor I` and `W=B_m...B_1`.  Since control `j` is touched
only once, a path from `0^m` back to `0^m` must use the `0->0` block `Q_j`
at that step.  Therefore, without assuming that the `Q_j` commute,

```text
PWP=|0^m><0^m| tensor Q_m...Q_1.
```

For a source projection `Q` and transport `U`, put `S=PUQ` and
`s=||S||_2^2`.  If the game compressor has norm at most `rho<1`, then

```text
tau(Q)-s=||(I-P)UQ||_2^2,
s-Re tau(S^*WS)>=(1-rho)s.
```

These are respectively the source deficit and the single return moment.
A global word relation `WU=U` would force `W=I`, whereas the perfect witness
only fixes one Gram vector.  Hence HNN covariance cannot replace the
compressed equation `PWPUQ=PUQ`.

Finally, the minimal controller cell admits a multiplicity orientation
`u_j`; after Hadamard its zero corner is `u_jQ_j`.  Finite wreath naming is
therefore exact in the intended type but does not universally select the
desired corner.  The construction has genuinely compressed the syntax to
the two displayed scalars, and has not proved them.
