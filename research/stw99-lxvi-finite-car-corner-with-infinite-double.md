---
rg: 2
id: stw99-lxvi-finite-car-corner-with-infinite-double
kind: claim
title: A simple finite CAR-containing algebra has an infinite two-by-two amplification
---

There exist a simple unital C\*-algebra `A` and a unital embedding

```text
psi : M_(2^infinity) -> A
```

such that the unit `1_A` is a finite projection but the unit of `M_2(A)` is
an infinite projection.

This is the exact construction target left by STW Problem LXVI, not a known
example.  It is stronger than merely asking for a simple finite but not
stably finite algebra: the latter is known, whereas this claim asks that a
CAR algebra occur unitally before the first infinite matrix amplification.

## Attempts

The obvious tensorial repair of a known finite non-stably-finite algebra does
not work.  If `M_2(A)` is infinite, then the unital inclusion of `M_2(A)` into
`A tensor M_(2^infinity)` already makes the latter's unit infinite; this is
`stw99-lxvi-car-stabilization-destroys-finite-seed`.  A successful construction
must therefore insert a coherent CAR tower non-tensorially, while preventing
the isometries in every finite amplification from becoming isometries of the
limit unit.
