---
rg: 2
id: titz-witzel-both-matchings-need-macroscopic-support
kind: claim
title: Both exact matchings need macroscopic support in the seven-relator Titz--Witzel gate
distinct_from:
  titz-witzel-trivial-second-matching-collapses-mark: That quantitatively treats a trivial or asymptotically trivial second matching; this uses the second coupling equation to reduce a trivial first matching to that case.
  titz-witzel-cyclic-affine-ansatz-has-linear-defect: That excludes one full-support reflection ansatz; this excludes every asymptotically trivial matching ansatz independently of the arbitrary permutation.
---

**THEOREM.**  In the exact-involution version `(TW8)--(TW10)` of the
seven-relator Titz--Witzel gate, a marked approximate solution cannot satisfy

```text
d_H(c_n,1) -> 0             or             d_H(e_n,1) -> 0.             (TBM1)
```

Equivalently, along a subsequence on which
`d_H(Y_n^8,1)>=epsilon>0`, both involutions `c_n` and `e_n` have support at
least a positive proportion of the permutation domain.  This remains only a
necessary condition: macroscopic support of both matchings does not construct
an approximate solution.

More quantitatively, if `delta_j` denotes the defect of the `j`-th coupling
word in `(TW9)`, then

```text
d_H(Y^8,1)
 <=296 delta_2+8 delta_3+16 delta_4+968 d_H(c,1).          (TBM2)
```

Together with `(TEM3)`, this gives asymptotic support lower bounds
`epsilon/968` for `c_n` and `epsilon/296` for `e_n` when the coupling defects
tend to zero and the mark stays at least `epsilon`.

---

### Proof

titz-witzel-both-matchings-macroscopic-proof
