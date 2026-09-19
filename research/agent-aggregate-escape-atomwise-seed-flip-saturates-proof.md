---
rg: 2
id: agent-aggregate-escape-atomwise-seed-flip-saturates-proof
kind: route
title: Conjugate by the Pauli seed flip and apply full reducing support in the opposite half
target: agent-aggregate-escape-atomwise-seed-flip-saturates
requires:
  - agent-aggregate-escape-forbidden-support-saturation
  - finite-pauli-seed-reducing-quarter-carrier
  - role-packed-bcs-gap-is-one-idempotent
---

The corrected `D_8` seed satisfies `CBC^*=BJ`.  The word `C` commutes with
the corrected shared BCS and role tuples.  On the `J=-1` sector it therefore
interchanges the two `B` spectral projections while fixing every `R_iP_i`,
which proves `(ASF4)` directly.  No new stable letter or HNN exactification
is required.

Distinct `R_i` are orthogonal role atoms, so the target idempotents are
pairwise orthogonal.  Summing `(ASF4)` gives `(ASF5)`.  The projection `B`
commutes with the shared BCS and role tuple, so `Q_-seed` is a reducing
carrier for that tuple.  Apply
`agent-aggregate-escape-forbidden-support-saturation` inside `Q_-seed`: the
reducing hull of `Q_-seed B_f` is `Q_-seed`.  Adding the already reducing
orthogonal carrier `Q_+` proves `(ASF6)`.

For approximate representations, exactify the fixed Pauli and role packets,
average the BCS tuple into their commutant, and use fixed-word telescoping.
This gives

```text
||D-Q_-seed B_f||_2<=K sqrt(E).
```

Apply `(AFS5)` with `delta=K sqrt(E)`.  Its `delta^2` term is `O(E)` and its
structural term is `O(sqrt(E))`, proving `(ASF7)`.

Finally, for projections `Q_1,D_1<=Q_mark=(1-J)/2`,

```text
tau(D_1)-tau(Q_1D_1)
 =tau((Q_mark-Q_1)D_1)
 <=tau(Q_mark-Q_1).                                   (1)
```

Use `(ASF7)` in `(1)` and the trace preservation of the corrected transport
to obtain `(ASF8)`.  The exact carrier gap gives

```text
tau(Q_1B_f)>=(beta/m)tau(Q_1)-O(sqrt(E)),
```

while canonical mark separation and `(ASF6)--(ASF7)` give
`tau(Q_1)->1/2`.  Hence the source mass stays bounded away from zero, and
`(ASF8)` is incompatible with `(ASF9)` for every fixed `eta>0` as `E->0`.
