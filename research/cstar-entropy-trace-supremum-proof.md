---
rg: 2
id: cstar-entropy-trace-supremum-proof
kind: route
title: Apply the variational principle and the trivial group character
target: cstar-one-bounded-entropy-is-canonical-trace-blind
requires: []
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
---

MacMahon's variational principle gives, for every unital C-star algebra `A`
with nonempty trace space,

```text
h(A)=sup_(tau in T(A)) h(M_tau),
```

and Theorem 8.1 gives `h^top(A)<=h(A)`.  Thus `h(A)` retains the supremal
value but no designation of which trace produced it.

For `A=C^*(G)`, the canonical group trace `tau_G` is one element of `T(A)`.
There is always another distinguished element: the trivial representation

```text
epsilon:C^*(G)->C,             epsilon(u_g)=1
```

is a character, its GNS von Neumann algebra is `C`, and the scalar algebra
has `h(C)=0`.  Hence

```text
h(C^*(G)) >= h(M_epsilon)=0.                              (1)
```

If `G` is nonhyperlinear, then `M_(tau_G)=L(G)` is not Connes embeddable and
its 1-bounded entropy has the conventionally forced value `-infinity`.
Equation `(1)` shows that this canonical-trace value is strictly hidden by
the trace supremum.  Conversely, the single aggregate `h(C^*(G))` contains
no label recovering `tau_G` or its summand from that supremum.  Thus the
variational-principle calculation alone does not certify nonhyperlinearity
merely from the presence of a negative or non-Connes-embeddable summand; an
argument using it needs independent input which isolates the canonical
trace.  No assertion is made about other scalar criteria carrying additional
structure.

The operator-system assertions are exactly MacMahon's Theorems 9.1 and 9.2:
the two invariants pass through the maximal C-star cover and may be computed
on a self-adjoint spanning set.  These statements provide an entropy input
for the three-dimensional systems recorded in the target, but assert no LP
or LLP detection theorem.  This proves each asserted boundary and does not
promote that absent connection to a route.
