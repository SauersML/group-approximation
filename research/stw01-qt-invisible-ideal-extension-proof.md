---
rg: 2
id: stw01-qt-invisible-ideal-extension-proof
kind: route
title: Factor an ambient quasitrace through the quotient using its trace-kernel ideal
target: stw01-qt-invisible-ideal-extension-principle
requires: []
---

Let `tau` be a bounded 2-quasitrace on `A`.  Its restriction to `I` is a
bounded 2-quasitrace, hence is zero by hypothesis.  Use the standard
trace-kernel lemma for bounded 2-quasitraces:

```text
N_tau={x in A: tau(x*x)=0}
```

is a closed two-sided ideal and `tau` induces a bounded 2-quasitrace on
`A/N_tau`.  This lemma follows from monotonicity,
`tau(x*x)=tau(xx*)`, and the quasitrace Cauchy--Schwarz/subadditivity
inequalities: they make `N_tau` a two-sided linear space and show that
changing a lift by an element of `N_tau` does not change the induced
quasitrace.

Since `tau` is zero on `I_+`, one has `I subset N_tau`.  Pulling the induced
quasitrace on `A/N_tau` back along the quotient map

```text
A/I -> A/N_tau
```

gives a bounded 2-quasitrace `bar_tau` on `Q=A/I` such that
`tau=bar_tau q`.  The hypothesis on `Q` makes `bar_tau` a trace, and its
pullback `tau` is therefore a trace.
