---
rg: 2
id: twisted-leavitt-k0-states-can-be-chosen-halving-invariant
kind: claim
title: If a twisted Leavitt factor admits a K_0 state, it admits one invariant under the halving map
distinct_from:
  twisted-leavitt-corner-fullness-equals-absence-of-k0-states: that is Theorem E, the equivalence between corner fullness and the absence of any state; this shows that when a state exists one can be chosen self-similar under the halving map F, with forced values m^-k on the tower F^k(u).
  anti-central-state-obstruction-equals-stable-finiteness: that is the Hahn–Banach criterion for the existence of a state from positivity of the unit class; this is a fixed-point normalization of states along the Leavitt self-similarity.
artifacts:
  - research/artifacts/halving-invariant-k0-states-2026-09-12.md
---

In the Theorem E setting of `twisted-leavitt-corner-fullness-equals-absence-of-k0-states` (a Leavitt-visible
factor `A` of `F_q[L_(F_q)(1,d)^x]` with twist order `m`, unit class `u`, and the halving monoid map
`F: V(A) -> V(A)` induced by `Phi = M_m(e_H D(.))` with `F(m·u) = u`): if `(K_0(A), u)` admits a state, it
admits a state `s` with `s o F_* = s/m`. Such a state takes the value `m^(-k)` on `F_*^k(u)`.

Consequences:
- the cyclic corner is full iff no halving-invariant state exists; at `(3, 2, 2)` this is the ternary
  corner `ternary-anti-invariant-swap-corner-is-full`;
- every state source, for instance a characteristic-three rank model moving `z`, can be averaged into an
  invariant one (Cesàro means along `F_*`).

This decides nothing: no state and no Cohn family is known. Proof: Section 2 of the artifact, route
`halving-invariant-k0-states-proof`.
