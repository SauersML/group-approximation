---
rg: 2
id: duplicate-selector-occurrence-seam-proof
kind: route
title: Separate common transport, split transport, and direct Whitehead cases
target: duplicate-selector-transports-retain-occurrence-seam
requires:
  - literal-selector-roots-force-center-chain
  - literal-prefix-three-root-swap-retains-typed-carriers
  - same-center-whitehead-gram-is-not-native-selector-gram
---

Conjugation preserves commutators, so the cross-commutation in `(ARC3)` gives
`(DAS1)` immediately.  If the two duplicates use different conjugators,
rewriting one in the other's coordinates leaves `r_B^(-1)r_A`; this proves
`(DAS2)` and shows that duplication alone supplies no relation on the
relative word.  Requiring both duplicate arms to remain in their own
authenticated Heisenberg cells puts them under the hypotheses of
`literal-selector-roots-force-center-chain`, proving the first branch.

Prefix cancellation gives

```text
y_ix_i=e_source,i,            x_iy_i=e_target,i.
```

The standard three-elementary calculation in characteristic two therefore
makes each `J_i` in `(DAS3)` an involutory full matrix unitary swapping those
two typed corners.  The exact finite typed model and the failure to identify
the ambient packet units are proved in
`literal-prefix-three-root-swap-retains-typed-carriers`.

If `J_i` centralizes the finite subgroup supporting `e`, it commutes with
`e`.  Hence `S_i^*S_i=S_iS_i^*=e`, and cancellation proves `(DAS4)`.
`same-center-whitehead-gram-is-not-native-selector-gram` shows why this
full-unitary identity cannot be substituted for the Gram of the prescribed
unequal selector occurrences.  These three cases exhaust the proposed
route and prove the target claim.
