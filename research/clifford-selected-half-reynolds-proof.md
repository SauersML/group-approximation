---
rg: 2
id: clifford-selected-half-reynolds-proof
kind: route
title: Enlarge both levels of the assignment pair by the commuting selector involution
target: clifford-selected-half-is-an-index-two-reynolds-surplus
requires:
  - central-sign-bcs-atoms-are-subgroup-reynolds-projections
  - one-bit-clifford-selector-halves-a-chosen-bcs-atom
  - subgroup-hecke-hnn-is-a-regular-safe-rank-actuator
---

The context group splits as `C=H_a directProduct <J>`.  Since `p` commutes
with `C`, adjoining it to both levels gives

```text
K_a=H_a directProduct <p>,
L_a=K_a directProduct <J>.
```

These subgroups embed in the selector packet.  Explicitly, if
`z=J^(1-a(v_0))x_(v_0)`, the packet is the semidirect product in which `q`
fixes `C` and sends `p` to `pz`; this realizes the defining commutator
relation and preserves `<C,p>`.

Reynolds averaging over direct products is multiplicative.  Subtracting the
two averages proves `(CSR3)`, and the central-sign atom identity gives
`(CSR4)`.  The established HNN actuator then supplies the stated local exit
and its dimension-independent HS payment.
