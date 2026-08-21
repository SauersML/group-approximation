---
rg: 2
id: graph-commutator-authenticates-paz-return
kind: claim
title: A graph commutator authenticates one projection return moment
distinct_from:
  pauli-zero-atom-removes-acceptance-source-deficit: that isolates a one-vector PAZ return scalar; this authenticates a projection-trace return.
  mixed-pauli-commutator-authenticates-one-capacity-cut: that treats leakage of one spectral cut; this captures internal phase and range leakage of an arbitrary verifier unitary.
  authenticated-pauli-branch-needs-source-saturation: that proves a branching recurrence; this supplies its authenticated projection mark.
---

For a projection `G` and unitary `W` in a finite tracial matrix algebra, a
fixed two-stage graph amplification produces involutions `A,B` whose
commutator `C=ABAB` satisfies

```text
||C-I||_2^2
 =2[tau(G)-Re tau(GWG)]+||(I-G)WG||_2^2.
```

The leakage term is between zero and twice the return energy, so

```text
1/4||C-I||_2^2 <= tau(G)-Re tau(GWG)
                <=1/2||C-I||_2^2.
```

Thus one mixed involution coordinate authenticates the whole projection
return moment with universal constants.  This theorem does not promote the
current PAZ Gram vector to a positive-density projection; that remains the
application boundary.
