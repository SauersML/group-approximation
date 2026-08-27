---
rg: 2
id: finite-clifford-symplectic-section-obstruction
kind: claim
title: Binary Clifford blocks of rank at least two admit no multiplicative symplectic section
distinct_from:
  invariant-graph-clifford-phase: that computes which central phase survives in the infinite invariant-graph quotients and proves only a sign is available; this is a finite group-cohomological statement about one finite Clifford block, with no G, no coset space and no marked word in it.
  wall-energy-amplification: that says a wall's trace energy is free under diagonal tensor powers; this says a Clifford lift's multiplicative defect is not removable at all inside a fixed finite block, which is why the surviving dilution mechanism has to be direct sums rather than tensor powers.
  clifford-block-amalgam-residually-finite: that is a residual finiteness statement about finite central amalgams of Clifford lamp blocks; this is the nonsplitness of the symplectic-to-Clifford extension inside a single block.
artifacts:
  - research/artifacts/hyperlinear-q34-literature-2026-08-18.md
---

Let `A` be a finite abelian group and let

```text
1 → V_A → C(A) → Sp(V_A) → 1,        V_A = A ⊕ Â,
```

be the Clifford extension of the symplectic group by the phase space.
Galindo (`arXiv:2603.24743`, v2 2026-08-11) proves this splits as a
semidirect product **iff `4 ∤ |A|`**, the obstruction being carried entirely
by the 2-primary component; Korbelář--Tolar (`arXiv:2606.08215`) obtain the
same threshold for multipartite systems.

**Claim (the instance this program needs).**  For `A = (ℤ/2)^n` — the qubit
blocks produced by `vertex-supported-symplectic-completion`, of binary
symplectic rank `2n` — the extension splits only for `n = 1` and is nonsplit
for every `n ≥ 2`.  Equivalently, for `n ≥ 2` there is **no** group
homomorphism `Sp(V_A) → C(A)` splitting the projection: no rule assigning a
Clifford element to each symplectic transformation multiplicatively.

**Design constraint this imposes.**  A finite-block construction for the
minimal marked graph may not be organised around "extend the partial
symplectic action to the block, then choose the canonical Clifford lift":
there is no canonical multiplicative lift, before any asymptotics are
considered.  What remains open, and is what
`minimal-marked-graph-crossed-product-ce` actually needs, is far weaker —
that the cocycle *restricted to the finitely many relations of a tested group
window* be made negligible in normalized `2`-norm, possibly only after
averaging over an ensemble of blocks.  Nonsplitness of the full extension
says nothing against that.

Two defects must be kept apart when this is measured, following Galindo's
`arXiv:2606.21751`: the phase-space-valued factor set `a_s(T,S) ∈ V_A` of the
extension above, and, after projective Clifford elements have been chosen,
the scalar Weil multiplier `c(g,h) ∈ U(1)` of the unitaries representing
them.  These are different obstructions and a construction can fail at either.

## Scope

Literature import for the splitting theorem; the specialization to
`A = (ℤ/2)^n` is the one-line divisibility check `4 | 2^n ⟺ n ≥ 2`.  Nothing
here is asserted about restricted subgroups of `Sp`, about partial actions,
about direct sums of blocks, or about asymptotic triviality in any norm —
all of which remain available.
