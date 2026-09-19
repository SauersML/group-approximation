---
rg: 2
id: named-odd-native-factor-carrier-audit-proof
kind: route
title: Classify the odd factor rows and check their source and target charts
target: named-odd-native-factor-rows-have-no-esb-common-carrier
requires:
  - primitive-native-hecke-relators-have-no-odd-mixed-occurrence
  - literal-whiteheads-give-gauged-moving-bridge-table
  - native-a1-b2-hecke-triangle-has-gl7-model
  - fine-idempotent-biaction-return-has-gl10-model
  - endpoint-whitehead-star-braid-synchronizes-native-gauges
  - b2-b3-pair-full-hecke-four-native-sectors
  - full-moving-hecke-packet-retains-q-kernel-profile
  - cross-row-native-diamond-cube-retains-common-c2-gauge
---

The primitive occurrence audit proves that the only primitive mixed
triangles involving the native and Hecke letters are even in the factors
`X_i` which occur twice in `J_i`; the remaining primitive odd factor is
`Y_i`.  Adding the subsequently established derived rows gives precisely
the three classes listed in the claim: the definition of `J_i`, the
commutator word defining an exposed `B_i`, and a Coxeter word containing
one `J_i` and the endpoint `W`.  The two-head and two-Whitehead relations
have two members of `(ONF1)` with odd parity and hence are not additional
single-factor rows.

`literal-whiteheads-give-gauged-moving-bridge-table` proves both assertions
for class 1: the exact full Grams and squares hold, but the reservoir factor
is `D_(i,k)`.  `native-a1-b2-hecke-triangle-has-gl7-model` gives the exact
finite fence for the first class-2 factorization and
`fine-idempotent-biaction-return-has-gl10-model` retains the fence after the
two-sided fine-support coefficient rows are added.  In contrast,
`b2-b3-pair-full-hecke-four-native-sectors` types only the commutator
outputs `B_2,B_3` on the full signed source and proves their common quarter
sector; it supplies no typing for the nonnormal commutator inputs.

For class 3, the endpoint star-braid theorem proves the odd relation and
gauge synchronization.  `full-moving-hecke-packet-retains-q-kernel-profile`
exhibits the exact compatible profile `QWQ=0`, so that odd row has no full
Hecke source Gram.  Finally the cross-row `C_2` fence checks that the first
relations mixing the two diamond rows are even under the surviving paired
dressing.  These facts establish the source/target classification and the
finite-menu conclusion.
