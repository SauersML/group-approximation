---
rg: 2
id: stw99-lxvi-quasitrace-obstruction-proof
kind: route
title: Evaluate an infinite matrix unit and its nonzero complement with a faithful quasitrace
target: stw99-lxvi-finite-seed-has-no-quasitrace
requires: []
---

Suppose `tau` is a nonzero bounded quasitrace on `A`.  Its zero set on
positive elements is an ideal: the quasitrace identities and
`tau(x* x)=tau(x x*)` give invariance under multiplication, and lower
semicontinuity gives closure.  Simplicity and `tau!=0` therefore make `tau`
faithful.

Extend `tau` to the standard matrix quasitrace `tau_2` on `M_2(A)`.  Since
the unit of `M_2(A)` is infinite, there is a projection `q<1` Murray--von
Neumann equivalent to `1`.  Quasitraces are invariant under this equivalence,
so

```text
tau_2(q)=tau_2(1).
```

The projections `q` and `1-q` commute, hence quasitracial additivity applies:

```text
tau_2(1)=tau_2(q)+tau_2(1-q).
```

Thus `tau_2(1-q)=0`.  But `1-q` is a nonzero positive element and the matrix
extension of a faithful quasitrace is faithful, a contradiction.  Hence no
such `tau` exists.  Restricting any quasitrace on `A` to a unital CAR
subalgebra would give its unique normalized trace after rescaling, so that
trace has no quasitracial extension.

