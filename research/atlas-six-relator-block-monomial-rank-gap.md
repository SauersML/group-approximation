---
rg: 2
id: atlas-six-relator-block-monomial-rank-gap
kind: claim
title: Binary block-monomial frames pay a sharp six-row gap
artifacts:
  - experiments/atlas_six_relator_block_monomial_verify.js
  - experiments/atlas-six-relator-block-monomial-rank-gap.json
distinct_from:
  atlas-multiplicity-two-escape-fails-five-saturated-rows: that evaluates one named non-block-monomial frame in dimension eight; this treats the whole block-monomial wreath class in every multiplicity.
  atlas-six-relator-has-no-natural-alternating-target: that treats natural permutation supports inside alternating groups; this treats linear frames over F2 on repeated natural four-dimensional GL4(2) modules.
  leavitt-regular-atlas-block-monomial-gap: that uses 20160-dimensional regular A8 blocks and the full atlas packet over complex unitaries; this uses four-dimensional binary blocks and only the six surviving relators.
  atlas-six-relator-regular-face-defect-floor: that asks for a normalized-HS floor on every complex regular common frame; this is an exact rank floor on a restricted finite-field frame class.
---

**ESTABLISHED.**  Let `rho:A8~=GL_4(F_2)` be the literal four-dimensional
chart used by the matrices in
`experiments/atlas-six-relator-relative-pieces.json`, and put

```text
rho_k(g)=diag(rho(g),...,rho(g)) in GL_(4k)(F_2).
```

Let `F in GL_(4k)(F_2)` be block monomial for the decomposition

```text
(F_2^4)^direct-sum k:
```

every block row and every block column of `F` contains exactly one nonzero
`4 by 4` block, and that block is invertible.  Evaluate factor one by
`rho_k` and factor two by `F^(-1)rho_k F`.  For the six literal words

```text
S_6={s_0,s_11,s_30,s_44,s_55,c_19243},
```

one has the sharp binary-rank inequality

```text
sum_(w in S_6) rank_F2(pi_F(w)-I_(4k)) >= k.          (BMR1)
```

Consequently no frame in the full wreath class
`GL_4(2) wr Sym(k)` solves all six relators, for any `k>=1`.

The equality cases are exactly the pure permutations of the `k` identical
four-dimensional summands.  For such a frame the five boundary words are
identity and `c_19243-I` has rank `k`.

## Atomic certificate

The dependency-free replay enumerates all `2^16` binary `4 by 4` matrices,
retains exactly `20160` invertible alignments, and evaluates the stored words
by literal matrix multiplication.  Its atomic census gives:

- minimum total six-row residual rank `1`;
- a unique minimizer, the identity alignment, with rank vector
  `(0,0,0,0,0,1)`;
- exactly one five-boundary-zero alignment, again the identity;
- `4176` collision-zero alignments, whose boundary rank sum is at least `3`,
  with exactly `10` attaining `3`.

The complete total-rank histogram and the FNV-1a checksum of the ordered
`20160` alignment/rank records are pinned in the JSON artifact.

## Scope

This is a wreath/block-monomial obstruction, not a claim about arbitrary
finite representations or arbitrary `GL_(4k)(2)` frames.  A surviving binary
frame must use genuine linear mixing between the natural four-dimensional
summands; a surviving complex regular frame may lie still farther outside
this coordinate class.

ROUTES

atlas-six-relator-block-monomial-enumeration-proof
