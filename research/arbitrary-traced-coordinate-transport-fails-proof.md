---
rg: 2
id: arbitrary-traced-coordinate-transport-fails-proof
kind: route
title: Use the literal group in constant reduced-group-algebra coordinates
target: arbitrary-traced-coordinate-transport-fails
requires:
  - literal-central-mark-corona-invisible
artifacts:
  - research/artifacts/left-right-finite-coordinate-obstruction-2026-08-19.md
  - non_mf_groups_exist.tex
---

## Direct counterexample

The canonical trace on `C*_r(E)` is faithful.  Use the constant sequence of
coordinates `A_n=C*_r(E)` and the exact maps `U_n(g)=lambda_g`.  The defining
relations give `[c,B]=1`, so `lambda_c` centralizes the Kazhdan base exactly.

The transported element is `d=tct^-1`.  The distinguished unsquared defect
is `u=[d,v_1]`, and `u^2=w`.  By `literal-central-mark-corona-invisible`,
`w` is a nontrivial element of `E`; hence `u!=1`.  Faithfulness of the
canonical trace therefore gives `||lambda_u-1||_2>0`.

Any transport theorem valid for arbitrary faithfully traced coordinates
would send the exact zero commutators of `c` to zero 2-norm commutators of
`d`, in particular `||lambda_u-1||_2=0`.  Contradiction.
