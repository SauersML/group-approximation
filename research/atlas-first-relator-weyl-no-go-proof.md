---
rg: 2
id: atlas-first-relator-weyl-no-go-proof
kind: route
title: Replay the one-row rational Bezout obstruction
target: atlas-first-rank-five-relator-kills-order-one-weyl-slice
requires:
  - atlas-three-mode-balanced-area-coefficient-table
artifacts:
  - experiments/atlas-rank5-balanced-area.json
  - experiments/verify_atlas_rank5_balanced_area.py
---

The negative-certificate clause in
`atlas-three-mode-balanced-area-coefficient-table` permits termination as soon
as the collected relations have gcd one.  The first deterministic packet row,
`root_12_1e`, has the single exact coefficient

```text
f(t) = 16953689 / 41287680.
```

Consequently

```text
f(t)-1 = -24333991 / 41287680
```

is a nonzero constant, and exact rational multiplication gives

```text
(-41287680 / 24333991) (f(t)-1) = 1.
```

The archived row is bound to the complete packet by the ordered-word SHA-256
`9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99` and
has sparse-table SHA-256
`bd205a6f30584f8f2edaecded6f9b98228573f3277333661118a72b05c5aeafd`.
The verifier reconstructs the packet, both hashes, the shifted relation, and
the Bezout identity over `Q`; its full mode recomputes the sparse row itself.

Any common root would make every `f_s(t)-1` vanish, contradicting the displayed
identity already for this first row.  Thus there is no complex common root,
in particular no non-torsion unit-circle order-one Weyl phase.  This proves the
stated no-go without making any assertion about the larger non-Heisenberg
two-unitary moment space.
