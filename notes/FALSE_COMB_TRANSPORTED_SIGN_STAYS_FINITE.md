# A transported Pauli sign does not force the missing support containment

Date: 2026-08-13

## Outcome

The smallest possible repair of the Pauli branch-transfer gate is false.
Let `U` be the comb compressor and let `x13(p001)` be the distinguished
carrier sign.  Exact Leavitt-prefix arithmetic gives

```text
U* x13(p001) U
```

as another involution commuting with `raw`, `z11`, `z001`, and `c11`.  It is
not in the original order-16 carrier cell, but adjoining it only produces

```text
D8 x C2 x C2
```

of order `32`.  Thus comb transport of the carrier sign is still a completely
finite phenomenon.  It cannot force the trace-`1/4` transported carrier under
the trace-`1/8` initial cut from
`TRUE_PAULI_BRANCH_TRANSFER_PACKET.md`.

The intersections make the failure sharper:

```text
<raw,z11,z001> intersect U*<raw,z11,z001>U = 1.
```

For the larger two-Pauli cell

```text
K=<x0,y0,raw,z1> = D8 x D8,
```

the intersection `K intersect U* K U` has order `2`.  Its only nonidentity
element is the canonical root sign `x13(1)`; in the transported copy its
preimage is the first Pauli center.  This element is not central in `K`, and
the overlap contains no carrier cut or coefficient multiplicity algebra.

Consequently the missing containment cannot be obtained from a single
transported spectral sign or from an intersection of these ambient finite
subgroups.  The calculation redirects the attack to the multiplicative
two-Pauli packet, where the raw compressor itself produces a second Pauli
factor and a genuine coefficient algebra.

## Reproducible certificate

The exact audit is
`experiments/atlas_pauli_transported_carrier.py`; its checked output is
`experiments/atlas-pauli-transported-carrier.json`.  It uses exact prefix
arithmetic and has no random choices.  It was run on one MSI core and
completed in seconds; no local code was run.

