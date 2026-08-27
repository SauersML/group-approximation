---
rg: 2
id: cstar-one-bounded-entropy-is-canonical-trace-blind
kind: claim
title: C-star 1-bounded entropy takes a supremum over traces and cannot isolate the canonical group trace
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
distinct_from:
  cartan-algebras-are-strongly-one-bounded: that bounds Hayes entropy of one fixed tracial von Neumann algebra from a Cartan inclusion; this concerns MacMahon's C-star invariant aggregated over every trace.
  goldbring-sinclair-max-u-group-witness-is-trace-blind: that fences a maximal-tensor norm witness because the full group C-star algebra has many traces; this identifies the same canonical-trace blindness in the new C-star 1-bounded entropy variational principle.
---

MacMahon, arXiv:2608.15409v1, defines C-star invariants `h(A)` and
`h^top(A)` and proves

```text
h^top(A) <= h(A),                                      (CBE1)
h(A)=sup_(tau in T(A)) h(M_tau).                       (CBE2)
```

Here `M_tau` is the GNS von Neumann algebra of the trace `tau`.  Equation
`(CBE2)` is the variational principle (Theorem 6.1 as specialized in the
introduction), and `(CBE1)` is Theorem 8.1.

For a full group C-star algebra, the canonical group trace is only one
term in the supremum.  Even if its GNS algebra `L(G)` is non-Connes-
embeddable and hence has entropy `-infinity`, any other character with
larger entropy dominates `(CBE2)`.  Therefore

```text
entropy of C^*(G) alone does not promote a non-CE trace to the
canonical group trace and cannot by itself certify non-hyperlinearity. (CBE3)
```

This is a fence, not a dismissal of entropy at a fixed trace: Hayes's
von Neumann invariant can still constrain `L(G)` once the canonical trace
has already been isolated.

The paper also defines both invariants intrinsically for an operator system
`V` through its maximal C-star cover and proves that they can be computed
from a self-adjoint spanning set (Theorems 9.1 and 9.2).  This makes the
three-dimensional systems in
`llp-failure-has-three-dimensional-hyperrigid-witness` legitimate finite
entropy inputs, but no theorem in either paper says entropy detects LP or
LLP.  That possible connection is a research direction, not an established
route.  MacMahon's final remark further identifies `h^top(A)=-infinity`
with absence of any matricially finite quotient; this is an operator-norm
quotient property, not a canonical-trace hyperlinearity criterion.
