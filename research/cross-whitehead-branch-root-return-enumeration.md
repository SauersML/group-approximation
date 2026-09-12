---
rg: 2
id: cross-whitehead-branch-root-return-enumeration
kind: route
title: Hash exact exposed-row states and classify the repeated-Whitehead branch-root returns
target: cross-whitehead-sandwiches-branch-roots-into-signed-normalizer
requires:
  - two-depth-one-nonnormal-roots-do-not-return-cross-whitehead
  - signed-hecke-normalizer-has-eight-external-root-returns
  - cross-branch-partial-whiteheads-have-finite-wreath-gauge-model
---

Construct the `2688` words `(CWR1)` and the `304` individually nonnormal
roots `(CWR2)`.  For each source/native target and each occurrence order,
group the first words by the exact prefix-normal-form matrix

```text
w^(-1)x_28(1)w.                                      (CWRP1)
```

There are respectively `880,90,1117,104` distinct states for
`(Q,WR),(Q,RW),(J_1Q,WR),(J_1Q,RW)`.  Precompute the `4096` positive-sign
elements in each set `K_iL_0^(+)K_i`.  A second-occurrence state passes the
exposed-row test exactly when its matrix hash lies in the relevant finite
set.  This reduces the exhaustive traversal to `1128560` state transitions.

Expanding the state multiplicities and excluding equal root positions gives
the exposed-row survivor counts

```text
(426,426), (424,424), (0,0), (0,0),                  (CWRP2)
```

for the same four target/order cases, with the pair in each entry referring
to branches zero and one.  Direct exact conjugation by all remaining nine
signed generators leaves

```text
(12,12), (0,0), (0,0), (0,0).                        (CWRP3)
```

The artifact asserts these counts and checks that every survivor in
`(CWRP3)` has its three-factor word equal as a matrix to `K_i`, its root
position in `{6->8,9->8}`, and its coefficient in the branch-specific sets
`(CWR4)--(CWR5)`.

Finally multiply the two-by-two block of `K_i` by an incoming root at
coordinate `8`.  Orthogonality kills its row-eight component for precisely
the listed branch-supported coefficients, giving `(CWR6)`.  Prefix
cancellation proves `(CWR7)`, and the known nonconstant normalizer positions
`6->7,9->7` prove `(CWR8)` independently of the enumeration.
