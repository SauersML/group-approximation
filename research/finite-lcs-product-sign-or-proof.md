---
rg: 2
id: finite-lcs-product-sign-or-proof
kind: route
title: Homogenize branch rows and priority-decompose the odd selector sector
target: finite-lcs-product-sign-is-exact-or
requires:
  - odd-selector-priority-decoding
---

For completeness, choose a perfect marked representation of branch `i`.
Represent `Z_i` by `-1` and its payload by that branch representation.  For
`j != i`, represent `Z_j` and every branch-`j` payload variable by `1`.
Equation `(LOR3)` is then respectively the original marked branch equation
or a trivial identity.  Define every fresh `Y_(k,x)` as `Z_k x`.  All
commutation rows hold, and `(LOR5)` holds with `J=-1`.

For soundness, let `pi` be an exact representation in a finite tracial
algebra and put

```text
E=(1-pi(J))/2.
```

On `E`, equation `(LOR5)` says that the commuting selector signs have odd
parity.  Apply `odd-selector-priority-decoding`:

```text
P_i=(1-pi(Z_i))/2,
Q_i=E P_i product_(j<i)(1-P_j),
sum_i Q_i=E.                                                (LOR6)
```

If `E` is nonzero, some `Q_i` is nonzero (indeed one has trace at least
`tau(E)/m`).  The global commutation rows make `Q_i` commute with every
branch-`i` payload.  On this corner `Z_i=-1`, so `(LOR3)` becomes

```text
product_(x in I) pi(x)=(-1)^b Q_i,                         (LOR7)
```

and the original within-row commutation relations are unchanged.  Hence
the corner is a perfect representation of `L_i` with `J_i=-1`.

An approximate marked matrix sequence defines such an exact representation
in its tracial matrix ultraproduct.  A nonzero `Q_i` has positive
ultraproduct trace, and its coordinate corners (after ignoring a set outside
the ultrafilter) form a tracial matrix ultraproduct.  Therefore `(LOR7)` is
an honest marked matrix-ultraproduct branch model.  Since there are only
finitely many branches, the index `i` is fixed after the priority
decomposition; no model-dependent infinite choice or uniform quantitative
rounding is required.

