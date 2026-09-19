---
rg: 2
id: maximal-forbidden-atom-has-a-named-positive-half
kind: claim
title: One maximal forbidden BCS atom is a named Reynolds surplus with an optional balanced half
distinct_from:
  shared-bcs-matrix-only-supercritical-atom-selection: That additionally asks for authenticated next-carrier incidence; this completes only the operator-valued selection and reduces the remaining task to transporting one chosen piece.
  non-ce-bcs-has-finite-dimensional-forbidden-mass-gap: That supplies the scalar sum of all forbidden masses; this pigeonholes one atom and retains it as a literal selector projection.
---

**ESTABLISHED.**  Let the fixed non-CE BCS have `M` forbidden context types
in total and robust forbidden-mass constant `beta>0`.  On any reducing
carrier `Q<=Q_-`, let `E_i=QP_i` denote its forbidden assignment pieces.
Choose `i_*` with maximal trace.  Then, after the fixed local rounding used
by the robust BCS gap,

```text
tau(E_(i_*))
 >=(beta/M)tau(Q)-C sqrt(E).                            (MFA1)
```

The projection `E_(i_*)` already retains the complete operator/type data;
no truth-table router or Clifford selector is needed for that purpose.
Indeed `central-sign-assignment-atom-is-index-two-reynolds-surplus` writes
the uncut atom as

```text
P_(i_*)Q_-=e_(H_(i_*))-e_<H_(i_*),J>.                  (MFA1a)
```

Thus `E_(i_*)` is the compression to `Q` of one explicitly named
index-two subgroup-Reynolds surplus.  The no-loss mass bound `(MFA1)` is the
strongest local one-type interface for the subgroup-HNN/first-hit lane.

Apply `one-bit-clifford-selector-halves-a-chosen-bcs-atom` and put
`A_*=E_(i_*)R_(i_*)`.  It is a genuine selected type projection obtained
from the same original shared-variable tuple, and

```text
tau(A_*)
 >=(beta/(2M))tau(Q)-C_* sqrt(E).                       (MFA2)
```

The half-selector is therefore optional: it is useful only for interfaces
which specifically need a balanced Pauli child.  It should not be inserted
merely to name the maximal atom, because that loses a factor two and
`one-bit-selector-cannot-orient-paired-frame-hard-cycle` proves that the
selector sign cannot also orient the paired-frame reverse reservoir.

Thus simultaneous transport of every forbidden type is not needed.  What
remains is not scalar or operator selection but a payload-sensitive
incidence/escape word for this representation-dependent choice from a fixed
finite menu.
