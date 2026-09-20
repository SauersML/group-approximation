---
rg: 2
id: some-module-quotient-has-a-nonzero-liftable-kernel-class
kind: claim
title: Some module quotient has a nonzero reduced quotient-kernel K-class that lifts from the middle algebra
distinct_from:
  some-nonexact-group-has-a-k-inexact-module-triple: "Equivalent existential target with both directions wired; this formulation locates the nonzero class in K_j(C/J) and requires its six-term boundary to vanish."
  module-k-defect-is-liftable-quotient-kernel: "That is the established identification for each triple; this asks for a nonzero element for some triple."
artifacts:
  - research/artifacts/Cairn_Baum_Connes_General_Attempt.md
---

**OPEN.** There exist a countable group G, a countable abelian G-module V,
an invariant W≤V and j=0 or 1 such that, for X=V̂, Z=W^⊥,
C=C(X)⋊_rG, J=C_0(X\Z)⋊_rG, B=C(Z)⋊_rG, p:C→D=C/J and q̄:D→B,

```text
0 ≠ z ∈ im(p_*:K_j(C)→K_j(D)) ∩ ker(q̄_*:K_j(D)→K_j(B)).
```

Equivalently z≠0, q̄_*(z)=0 and ∂z=0 in K_(j−1)(J).
[Localization](module-k-defect-is-liftable-quotient-kernel.md) makes this
equivalent to the existing missing module triple, with routes in both
directions. It supplies the ordinary counterexample through that existing
route; it is not a second independent existence assumption.

## Attempts

- A nonzero extra algebra kernel E=ker q̄ supplies no nonzero liftable
  K-class. Even a class of K_j(E) may die in K_j(D).
- Every bounded positive trace on D kills candidate degree-zero classes
  by [the full trace theorem](module-quotient-k0-defects-are-trace-invisible.md).
  E is also the [tracial GNS radical](amenable-kernel-extra-kernel-is-tracial-gns-radical.md),
  so maps into faithfully traced algebras kill E, not just its canonical
  trace. These restrictions do not imply z=0; the
  [torus class](torus-has-nonzero-k0-class-invisible-to-every-trace.md)
  demonstrates that distinction without constructing a defect here.
- A surviving construction must verify nonzeroness in K_j(D), quotient
  vanishing, and zero boundary. No such construction is supplied.
