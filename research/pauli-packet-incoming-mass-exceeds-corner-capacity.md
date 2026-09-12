---
rg: 2
id: pauli-packet-incoming-mass-exceeds-corner-capacity
kind: claim
title: The transported raw/comb Pauli involutions carry incoming mass above their target corner's capacity
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
  - notes/TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md
  - research/artifacts/pauli-overlap-dichotomy-2026-08-20.md
  - experiments/atlas_transported_coefficient_raw_character_mixing.py
  - experiments/atlas-transported-coefficient-raw-character-mixing.json
  - experiments/verify_pauli_incoming_mass.py
distinct_from:
  atlas-fractional-pauli-return-network: that asks for a weighted network over many states whose rational reproduction number exceeds one; this is the single-corner mass budget of two named transported involutions, and if true it says the search that node describes has already succeeded at one corner.
  atlas-supercritical-pauli-branching-cycle: that asks for an integer branch incidence matrix with a supercritical strongly connected component; this asserts a numerical inequality between Hilbert-Schmidt masses at one corner.
  pauli-two-child-transfer-packet: that is the exact two-child cell with its trace-1/8 children; this is a mass budget for transported coefficient involutions into a trace-1/2 corner.
---

**ESTABLISHED.**  In the fixed raw/comb Pauli packet, let `F_epsilon` be the
four raw coefficient-character cuts, put `Q=sum_epsilon F_epsilon`, and let

```text
T_i=comb^* B_i comb,   X_i=Q T_i Q,   i=0,1.
```

Thus `tau(Q)=q=1/2`.  The exact rational block tables proved in
`transported-coefficient-raw-character-isotropic-mixing` sum to

```text
||X_0||_2^2 = 3/8,   ||X_1||_2^2 = 1/4.                           (PIM0)
```

Indeed the first table has four diagonal entries `21/256` and twelve
off-diagonal entries `1/256`; the second has four diagonal entries `5/128`
and twelve off-diagonal entries `1/128`.  Orthogonality of the cuts and
cyclicity identify the sums with the two compressed squared masses.  Hence
the mass budget is

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

Thus supercriticality is already present in the packet, and the open problem
narrows to what the mixed relations force the compulsory `5/32` of overlap to
do.  `verify_pauli_incoming_mass.py` replays all sums from the checked JSON
using exact rational arithmetic.

## Superseded audit and interpretation

- **Why the earlier node was open.**  The overlap dossier predated the exact
  transported-coefficient block tables, so it correctly reported that the
  operators and `5/8` sum were then unnamed.  The later table computation
  supplies exactly the missing data and supersedes that audit.
- **It does not conflict with the canonical-network gate.**  A reader may
  expect a clash with `supercritical-network-needs-noncanonical-cuts`, which
  forbids canonical supercritical networks.  There is none: that gate forbids a
  canonical supercritical configuration whose *overlap vanishes*, and `(PIM3)`
  produces one whose overlap is bounded strictly away from zero.  The exact
  model pays the `5/32` too.
