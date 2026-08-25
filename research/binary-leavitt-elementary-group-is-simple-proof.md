---
rg: 2
id: binary-leavitt-elementary-group-is-simple-proof
kind: route
title: Detect a nonzero elementary root inside every nontrivial normal subgroup
target: binary-leavitt-elementary-group-is-simple
requires:
  - leavitt-center-is-coefficient-field
artifacts:
  - GroupApproximation/Leavitt/RootDetectionBinary.lean
---

Use the internal root-detection argument formalized in
`Leavitt/RootDetectionBinary.lean`; no exchange-ring normal-subgroup theorem
is needed.

Let `N` be a nontrivial normal subgroup of `EL_n(R)` with `n>=3`, and choose
`g in N`, `g!=1`.  Commutators of `g` with elementary transvections and spare
indices reduce, by explicit matrix identities, to an element of `N` whose
defect is supported in one row.  The binary Leavitt family supplies split
annihilators for the possible nonzero inverse matrix entry.  Strong
two-sided division in `R` then converts a nonzero coefficient of that row
into a root element

```text
e_ij(x) in N,                  x!=0.                    (BLS1)
```

The only exceptional reduction would make `g` a scalar central unit.  The
internal kill-word center calculation
`leavitt-center-is-coefficient-field` says that the only such unit over
`F_2` is one, contradicting `g!=1`.

Finally, if `(BLS1)` holds, strong two-sided division gives `a,b` with
`axb=1`.  Two elementary commutator identities and index conjugacy put every
elementary generator in `N`; hence `N=EL_n(R)`.  Thus every normal subgroup
is trivial or the whole group.  The Lean theorem
`isSimpleGroup_elementaryGroup_binaryLeavitt` discharges every hypothesis
internally.
