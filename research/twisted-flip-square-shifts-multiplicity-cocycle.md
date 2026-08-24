---
rg: 2
id: twisted-flip-square-shifts-multiplicity-cocycle
kind: claim
title: Twisting a packet flip square shifts rather than removes its multiplicity cocycle
artifacts:
  - research/artifacts/finite-adaptive-hs-escape-audit-2026-08-24.md
distinct_from:
  commuting-automorphism-cocycle-forces-multiplicity: that treats commuting stable letters and reads the packet cocycle as an external divisibility law; this permits a fixed central commutator twist and computes the quotient cocycle exactly.
  controlled-pauli-commutator-is-and-times-multiplicity-commutator: that factors one controlled-gate commutator into packet and external factors; this applies the factorization to a complete automorphism square and proves the sharp amplification no-go.
  atomwise-schur-pauli-cycle-return: that asks for a positive-density half-to-quarter return; this proves that changing only the scalar commutator of one flip square cannot supply such a return.
---

Let `B` be a finite group, let `alpha,beta in Aut(B)` commute, and let `T`
be an irreducible `B`-module invariant up to equivalence under both
automorphisms. Choose implementers `A,D` on `T` with

```text
A D = zeta D A.                                           (TFS1)
```

Let `c in Z(B)` be fixed by `alpha,beta`, and write `omega` for the scalar
by which `c` acts on `T`. In a representation of

```text
<B,u,v |
 u b u^(-1)=alpha(b), v b v^(-1)=beta(b), [u,v]=c>       (TFS2)
```

whose `T`-isotypic carrier is invariant under `u,v` and is identified with
`T tensor C^m`, there are multiplicity unitaries `R,S` such that

```text
u=A tensor R,        v=D tensor S,
[R,S]=omega zeta^(-1) I_m.                               (TFS3)
```

Consequently, if `omega zeta^(-1)` has order `r`, then `r` divides `m`.
The commutator twist therefore **shifts** the projective packet cocycle to
the quotient `omega zeta^(-1)`; it does not authenticate a projection or
produce a rank-changing conjugacy.

This is sharp in normalized Hilbert--Schmidt norm. For fixed `r` and
arbitrarily large `m`, exact Weyl pairs on the largest `r`-divisible
subspace, extended arbitrarily on the remainder, violate `(TFS3)` on fewer
than `r` dimensions. Their squared normalized-HS defect is at most

```text
4(r-1)/m.                                                (TFS4)
```

Thus no fixed twisted flip square has a dimension-independent marked
energy gap.

For the Schur predicate flip square, the packet cocycle on a forbidden
simple is `zeta=-1`. Replacing the usual relation `[u,v]=1` by `[u,v]=J`
on the marked `J=-1` sector makes the forbidden external gauges commute:

```text
omega zeta^(-1)=(-1)(-1)^(-1)=1.                        (TFS5)
```

On the allowed orbit sum, where the packet flip implementers commute, the
same twist instead asks the external gauges to anticommute. Hence the twist
moves the parity cost from forbidden to allowed packet mass. It cannot by
itself return a forbidden half flag to a quarter flag or force escape from a
positive-density carrier. A successful use must still amplify independent
quotient cocycles beyond the current residual multiplicity, or couple the
square to a separate positive-density capacity inequality.

