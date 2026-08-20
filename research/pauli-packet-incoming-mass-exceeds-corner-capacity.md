---
rg: 2
id: pauli-packet-incoming-mass-exceeds-corner-capacity
kind: claim
title: The transported raw/comb Pauli involutions carry incoming mass above their target corner's capacity
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
  - notes/TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md
  - research/artifacts/pauli-overlap-dichotomy-2026-08-20.md
distinct_from:
  atlas-fractional-pauli-return-network: that asks for a weighted network over many states whose rational reproduction number exceeds one; this is the single-corner mass budget of two named transported involutions, and if true it says the search that node describes has already succeeded at one corner.
  atlas-supercritical-pauli-branching-cycle: that asks for an integer branch incidence matrix with a supercritical strongly connected component; this asserts a numerical inequality between Hilbert-Schmidt masses at one corner.
  pauli-two-child-transfer-packet: that is the exact two-child cell with its trace-1/8 children; this is a mass budget for transported coefficient involutions into a trace-1/2 corner.
---

In the fixed raw/comb Pauli packet of the atlas presentation, let `Q` be the
transported coefficient corner of trace `q = 1/2` and let `X_1, X_2` be the two
transported coefficient involutions compressed into it.  The claim is the mass
budget

```text
M_tot = ||X_1||_2^2 + ||X_2||_2^2 = 5/8,                             (PIM1)
```

so that by `contraction-branch-capacity-forces-collision` the reproduction
number is

```text
R = M_tot / q = 5/4 > 1,                                             (PIM2)
```

and the compulsory ordered cross-Gram overlap is

```text
sum_(a != b) ||X_b^* X_a||_2^2 >= M_tot^2/q - M_tot = 5/32.          (PIM3)
```

If `(PIM1)` holds then supercriticality does not have to be constructed: it is
already present in the packet the repository has, and the open problem narrows
to what the mixed relations force the compulsory `5/32` of overlap to do.

## Attempts

- **The number is not in the notes and must be recomputed.**  This is the
  reason the claim is open.  `notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md` and
  `notes/TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md` record the exact traces
  `tau(E)=tau(R_0)=tau(R_1)=1/8`, `tau(F)=1/4`, `tau(F_eps)=tau(G_eta)=1/8` and
  `tau(F_eps G_eta)=1/64`, and a grep of `notes/` for `5/8` returns nothing.
  So `(PIM1)` is an assertion from outside this repository about which two
  involutions are meant and what their compressed masses are.  Until the two
  operators are named against the packet notes and their `||.||_2^2` recomputed
  by the same exact rational group-algebra arithmetic that produced `1/64`, the
  claim is unverified.
- **What would falsify it cheaply.**  The four raw character cuts have total
  trace `1/2` and pairwise transported masses `1/64`; a budget of `5/8` into a
  corner of trace `1/2` must therefore come from operators substantially larger
  than the character-level blocks, whose guaranteed coverage
  `supercritical-network-needs-noncanonical-cuts` caps at `1/2` of a source cut.
  Identifying the two involutions and checking whether their masses can exceed
  the character budget is the single computation this node needs.
- **It does not conflict with the canonical-network gate.**  A reader may
  expect a clash with `supercritical-network-needs-noncanonical-cuts`, which
  forbids canonical supercritical networks.  There is none: that gate forbids a
  canonical supercritical configuration whose *overlap vanishes*, and `(PIM3)`
  produces one whose overlap is bounded strictly away from zero.  The exact
  model pays the `5/32` too.
