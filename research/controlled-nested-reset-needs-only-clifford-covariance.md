---
rg: 2
id: controlled-nested-reset-needs-only-clifford-covariance
kind: claim
title: Rewrite the finite controlled reset so every corner block is used only through Clifford covariance
distinct_from:
  controlled-pauli-corner-has-clifford-groupification: that classifies one completed controlled Pauli block; this asks whether the entire finite reset calculation factors through those representation-uniform conjugation actions.
  q-masa-to-fresh-packet-morita-bridge: that asks for the completed positive-density packet bridge; this isolates its first ordinary-group promotion gate.
---

Give the constant-depth controlled nested reset cell as a finite list of
Pauli generators and controlled operations, then replace every occurrence of

```text
(1-c)+c u
```

by the stable letter of a Pauli-completed CZ or CNOT semidirect product. Prove
that the full restriction/multiplicity calculation uses each stable letter
only by conjugating Pauli words. Equivalently, after writing every marked
representation as

```text
spin packet tensor multiplicity space,
```

the arbitrary multiplicity involutions `V` from `(CPC4)` must cancel from
every incidence map and from the proposed contracting functional.

The required output is an explicit finite presentation and its complete
marked type/restriction table. That table must still have an
amplification-stable nonnegative functional with contraction factor less than
one after all complementary types are included.

## Attempts

- **Literal corner equality. Dead.** It is excluded by
  `central-corner-block-is-not-a-group-word`.
- **Pauli completion. Active.**
  `controlled-pauli-corner-has-clifford-groupification` makes the desired
  block covariance exact in every marked representation.
- **Using the stable-letter sign as data. Dead without another constraint.**
  The two extensions `C_Z tensor V` are both honest representations. Any
  trace, spectral projection, or branch label read directly from the stable
  letter sees the arbitrary involution `V` and is not the distinguished
  controlled block.
- **Covariance-only replay. Open.** The repository has the reported
  two-level `C^64` model and its `3/4` ray arithmetic, but not a generator by
  generator replay showing that all incidences depend only on conjugation.
  Producing that replay is now a finite falsifiable calculation.
