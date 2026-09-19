---
rg: 2
id: fixed-extraspecial-packet-is-morita-neutral-for-code-rounding
kind: claim
title: A fixed extraspecial packet is Morita-neutral for code rounding
distinct_from:
  fixed-k-code-product-gap-is-a-twisted-intertwiner-test: that computes a generator conjugation gap for an already exact direct product; this shows that packet-relative centrality cannot exactify the multiplicity code algebra.
  positive-rate-tanner-tests-have-contextual-models: that constructs the class-two contextual escape; this proves the escape survives tensoring with the fixed packet.
---

# A fixed extraspecial packet is Morita-neutral for code rounding

ESTABLISHED. Let `K` be the extraspecial two-qubit Pauli group supplied by
the homogeneous Magic-Square packet, with central involution `J`. In every
finite-dimensional representation on which `J=-I`, the finite Stone-von
Neumann theorem gives

```text
H = C^4 tensor M,          pi(K)=Pauli_2 tensor I_M.       (ME1)
```

Consequently

```text
pi(K)' = I_4 tensor B(M).                                (ME2)
```

Thus any logical reflections required merely to commute with the fixed
packet have the form `I_4 tensor Q_i`. Every parity-face product defect,
pair-commutator defect, and normalized Hilbert--Schmidt distance between
such logical words equals the corresponding quantity for the `Q_i` on `M`.

In particular, tensoring any exact class-two/sparse-Clifford-cycle contextual
model by `I_4` produces an exact packet-relative model with exactly the same
failure of global commuting/code-PVM rounding. The packet cannot improve the
same-Hilbert decoder: it only exposes the unrestricted multiplicity algebra
where the original obstruction lives.

The approximate version has the same endpoint. Finite-group HS stability
can first correct an approximate `K` packet, and averaging over `K` moves
approximately central logical observables near `(ME2)`. Neither operation
constrains the resulting operators on `M`. A useful construction must couple
the code variables to noncentral `K` directions through the finite
twisted-intertwiner test, not merely impose packet-relative centrality or
repeat the packet at positive density.

## Consequence

The fixed Magic-Square packet does not close
`operator-unique-neighbor-cosystolic-rounding` or
`repeated-ldpc-adjoint-face-hamiltonian-gap`. Their contextual multiplicity
escape survives unchanged in the low-rate `Theta(r^2)` sampler regime.

