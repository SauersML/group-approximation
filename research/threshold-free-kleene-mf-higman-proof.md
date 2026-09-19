---
rg: 2
id: threshold-free-kleene-mf-higman-proof
kind: route
title: Enumerate a word proof, take the fixed point, and embed the MF obstruction
target: threshold-free-reverse-kleene-mf-higman
requires:
  - mikaelian-explicit-higman-embedding
  - mf-positive-controls
---

From `e`, construct a program which computes `S_e,w_e`, enumerates `R_e`,
dovetails all finite normal-closure certificates for

```text
w_e in <<R_e>>,
```

and halts on the first certificate.  Kleene's recursion theorem gives an
index `e_*` for this very program with its own compiled data.

The program cannot halt.  A certificate would prove `w_(e_*)=1`, whereas
`(TFM1)` would say `w_(e_*)!=1`.  Conversely, if `w_(e_*)=1`, one finite
derivation uses only finitely many eventually enumerated relators, so the
program would halt.  Hence

```text
w_(e_*)!=1 in Gamma_(e_*).
```

By `(TFM2)` every norm-corona homomorphism kills this nontrivial word, so
`Gamma_(e_*)` is non-MF.  The group is finitely generated and recursively
presented.  Apply `mikaelian-explicit-higman-embedding` to embed it effectively
in a finitely presented group `H`.  If `H` were MF, subgroup heredity from
`mf-positive-controls` would make `Gamma_(e_*)` MF, a contradiction.

For the one-generator compiler of
`marked-mf-radical-seed-gives-proof-triggered-compiler`, the fixed-point group
is already the finitely presented free product of the seed with `Z`; in that
instance the Higman step is unnecessary.
