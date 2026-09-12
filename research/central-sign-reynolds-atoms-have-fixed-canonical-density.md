---
rg: 2
id: central-sign-reynolds-atoms-have-fixed-canonical-density
kind: claim
title: Every embedded central-sign Reynolds atom has fixed canonical Plancherel density
distinct_from:
  central-sign-bcs-atoms-are-subgroup-reynolds-projections: that identifies the atom as a subgroup average; this computes its canonical trace in every ambient group containing the full context packet.
  non-ce-bcs-has-robust-approximate-energy-gap: that supplies a finite-matrix-only contextual obstruction; this density is already forced locally by the canonical group trace and uses no game gap.
  finite-subgroup-type-exclusion-is-already-nonhyperlinearity: that treats an arbitrary irreducible type; this records the exact scalar density of the assignment atom used by the Reynolds compiler.
artifacts:
  - notes/NONHYPERLINEAR_FINITE_MEMORY_REYNOLDS_AUDIT.md
---

Let `Gamma` contain an injective elementary-abelian context packet

```text
C=<x_1,...,x_k,J> ~= C_2^(k+1),
```

where the `x_i` are commuting involutions and `J` is an independent central
involution.  For `a in F_2^k`, put

```text
H_a=<x_i J^(a_i):1<=i<=k>,
Q_-=(1-J)/2,
A_a=e_(H_a)Q_-.
```

Then the canonical trace of every ambient group containing this packet
satisfies

```text
tau_Gamma(A_a)=2^(-(k+1)).                              (CSD1)
```

Consequently, in every canonical hyperlinear microstate sequence of
`Gamma`, after flexible exactification of the fixed packet,

```text
tr_d(A_a(U))->2^(-(k+1)).                              (CSD2)
```

The starting carrier in a Reynolds first-hit construction therefore already
has fixed positive normalized-HS density.  A robust non-CE BCS gap is not
needed to manufacture that density.  Its only possible role is to justify a
**finite-matrix-only** selection or exit inequality which fails for the
canonical regular representation and thereby removes the companion sectors
forced by subgroup-order orientation.

In particular, an unconditional first-hit actuator for one atom `A_a` is not
a local compiler lemma: combined with the established first-hit ledger it is
already a proof that the ambient group is nonhyperlinear.

