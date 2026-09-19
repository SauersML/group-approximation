---
rg: 2
id: a4-holonomy-gap-from-moment-simplex
kind: route
title: Thirty-one moment rounding and the classical separator rule out the exact A4 network
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-alignment-moment-simplex-rounding
  - atlas-a4-classical-mixture-trace-separator
---

Take a sequence in the hypotheses of `atlas-a4-holonomy-coherence-gap` and let
`tau_n` be its two-chart normalized trace state.

For each of the thirty context words `w_j`, the corresponding A4 vertex
relation is exact in `sigma_n`.  Every edge stable letter occurring when that
context word is transported back to the two chart vertices is `o(1)` from the
identity.  Since the graph is fixed, finite-word telescoping gives

```text
||w_j-1||_(2,tau_n) -> 0,          j=1,...,30.
```

The target hypotheses separately give

```text
||q_19243-1||_(2,tau_n) -> 0.
```

Therefore

```text
sum_j Re tau_n(w_j) + 6 Re tau_n(q_19243) -> 36.       (1)
```

By `atlas-a4-alignment-moment-simplex-rounding`, choose classical alignment
mixtures `tau_(nu_n)` whose values on exactly these thirty-one words differ
from `tau_n` by `o(1)`.  Equation `(1)` then implies

```text
sum_j Re tau_(nu_n)(w_j) + 6 Re tau_(nu_n)(q_19243)
  -> 36.                                                (2)
```

But `atlas-a4-classical-mixture-trace-separator` gives for every `n`

```text
sum_j Re tau_(nu_n)(w_j) + 6 Re tau_(nu_n)(q_19243)
  <= 30,
```

contradicting `(2)`.  Hence no sequence satisfying the target hypotheses
exists.  In particular the asserted bound

```text
limsup (a_n^2+b_n^2) < 1/128
```

holds vacuously.

This route is strictly weaker than packet-central synchronization: it never
rounds the relative chart unitary, never selects one alignment, and never asks
for an operator direct-sum decomposition.  Only thirty-one scalar moments must
be rounded to the finite classical simplex.
