---
rg: 2
id: stw01-free-group-qt-invariance-equivalence-proof
kind: route
title: Use unique tensor traces forward and the finite AW-factor obstruction backward
target: stw01-kaplansky-iff-free-group-qt-invariance
requires: []
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Assume first that every bounded 2-quasitrace is a trace.  The reduced free
group algebra has its unique tracial state `tau_F`.  Every normalized
quasitrace on `A` is therefore a trace and extends to the product trace on
`A tensor_min C*_r(F_2)`.  Conversely every quasitrace on the tensor product
is a trace.  If `rho` is such a trace and `a in A_+`, then

```text
b -> rho(a tensor b)
```

is a positive tracial functional on `C*_r(F_2)`, hence equals
`rho(a tensor 1) tau_F`.  Linear extension in `a` shows
`rho=rho|A tensor tau_F`.  Thus restriction is bijective.  It and the
product-trace inverse are weak-* continuous, proving `(FG1)`.

For the converse, use the classical equivalence between failure of
Kaplansky's quasitrace conjecture and existence of a type `II_1` AW*-factor
`M` which is not a von Neumann algebra.  Such an `M` has a normalized
quasitrace but no tracial state.  Haagerup's criterion says that, for a
unital C*-algebra `C`, absence of tracial states is equivalent to proper
infiniteness of `C tensor_min C*_r(F_2)`.  Consequently

```text
QT_1(M) is nonempty,
QT_1(M tensor_min C*_r(F_2)) is empty,
```

because a unital properly infinite algebra has no normalized quasitrace.
The restriction map cannot be an affine homeomorphism for `A=M`, contrary
to condition 2.  This proves the equivalence.  The AW*-factor reduction and
Haagerup criterion are literature inputs, exactly as flagged by STW
footnote 54.
