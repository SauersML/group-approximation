---
rg: 2
id: atlas-pauli-rank-ledger-finite-model-proof
kind: route
title: Compute the Atlas denominators and amplify the binary rectangular Pauli cell
target: atlas-pauli-rank-ledger-has-finite-rectangular-model
requires:
  - atlas-a4-context-exact-regular-normalization
  - first-leavitt-weyl-cell-has-exact-rectangular-model
  - four-pauli-cross-gram-exact-completeness-firewall
---

`atlas-a4-context-exact-regular-normalization` gives `d=20160 k`.  Since

```text
20160=2^6*3^2*5*7=64*315,
```

all rank assertions in `(PRL1)--(PRL3)` follow by integer division.  In
particular

```text
5040 k=2(2520 k)=4(1260 k),
```

so the same quarter-carrier dimension is simultaneously compatible with a
degree-two and a degree-four full matrix algebra.  This is only a module
dimension assertion; it does not identify the two actions or their
multiplicity coordinates.

Specialize `first-leavitt-weyl-cell-has-exact-rectangular-model` to `p=2`.
For the standard Pauli matrices `X,Z`, the tuple `(PRL4)` has

```text
X_src Z_src=-Z_src X_src,
D_1D_2=-D_2D_1,        D_3D_4=-D_4D_3,
[D_i,D_j]=0            across the two pairs.
```

The identity transports the source pair to the first target pair and `SWAP`
transports it to the second.  Their adjoints give the exact return laws.
Noncentral Pauli words have normalized trace zero.  The first tensor factor
generates `M_2 tensor 1_2`, whereas the two target pairs generate all of
`M_4`.  Direct sum preserves every displayed relation and every normalized
trace and normalized-HS value.  Since `d/4=5040 k` is divisible by four, the
same model may be placed on every exact quarter carrier; taking `5040 k`
copies places it on the full `d`-dimensional ambient space if desired.

Thus all rank, finite-type, and local rectangular-table data survive in
finite matrices at every permitted amplification.  What fails is exactly the
extra common intertwining demanded by the open Atlas target.  The standard
polynomial calculation in
`four-pauli-cross-gram-exact-completeness-firewall` gives a positive residual
whenever one positive-mass contraction is asked to intertwine all four target
words into one source `M_2` factor.  Hence the missing information cannot be
recovered from the rank ledger proved compatible above.
