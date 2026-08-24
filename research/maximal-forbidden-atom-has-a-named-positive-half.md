---
rg: 2
id: maximal-forbidden-atom-has-a-named-positive-half
kind: claim
title: One maximal forbidden BCS atom has a named half carrying a fixed fraction of every reducing carrier
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

Apply `one-bit-clifford-selector-halves-a-chosen-bcs-atom` and put
`A_*=E_(i_*)R_(i_*)`.  It is a genuine selected type projection obtained
from the same original shared-variable tuple, and

```text
tau(A_*)
 >=(beta/(2M))tau(Q)-C_* sqrt(E).                       (MFA2)
```

Thus simultaneous transport of every forbidden type is not needed to obtain
positive selected mass.  What remains is not scalar selection but a
payload-sensitive incidence/escape word for this representation-dependent
choice from a fixed finite menu.

