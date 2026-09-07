---
rg: 2
id: full-mf-radical-linear-relator-inequality
kind: claim
title: Full MF radical is equivalent to one global linear inequality on a fixed finite relator set
distinct_from:
  uniform-finite-mf-obstruction: that is a finite test with a positive threshold, for the manuscript's literal group and one marked word; this is a global linear inequality controlling the whole generator tuple, for an arbitrary finitely generated group.
  hyperlinear-radical-presentation-compactness: that is the normalized Hilbert--Schmidt statement in epsilon-delta form, with the finite window depending on the tolerance; this is an operator-norm statement whose finite relator set does not depend on any tolerance.
  depthwise-opnorm-collapse-implies-mf-radical: that is the sufficiency direction with a sequence of finite tests, vanishing offsets and unrestricted constants; this asserts one finite test and one constant, and adds the forward direction.
  full-mf-radical-uniform-asymptotic-collapse: that is the qualitative collapse, in threshold form, for unitary-valued maps on the group whose multiplicative defect is measured on a finite set of pairs, with the test set and the threshold depending on the tolerance; this is one global linear inequality for bare unitary tuples evaluated on a fixed finite relator set.
  effective-transport-modulus: that asks for explicit numbers on the displayed relators of the literal group; the finite list and the constant here exist by compactness and are not asserted computable.
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `G=<g_1,...,g_m>` be finitely generated, `F_m` free on `x_1,...,x_m`,
and

```text
D(U)     = max_i ||U_i - I||_op,
Def_R(U) = max_(r in R) ||r(U) - I||_op.
```

If `Res_MF(G)=G`, then there are finitely many `r_1,...,r_s in F_m` with
`r_j(g)=1` and a constant `C>0` such that

```text
D(U) <= C Def_{r_1,...,r_s}(U)                          (LIN)
```

for every `d>=1` and every `U in U(d)^m`.  Conversely, if some finite set of
relations of `G` and some `C` satisfy `(LIN)`, then `Res_MF(G)=G`.

The finite relator set is produced by the hypothesis, so no finite
presentability is assumed, and the set does not depend on a tolerance.  For
the two-generated group of `defect-saturation-full-mf-radical` the statement
reads

```text
max(||U-I||_op, ||V-I||_op) <= C max_j ||r_j(U,V)-I||_op
```

for every pair of unitary matrices in every dimension, while the left regular
representation of that group solves the same equations exactly and
nontrivially.

Neither `r_1,...,r_s` nor `C` is asserted computable.  Once the threshold
`delta` of the compactness step is fixed, `C=max(2,2/delta)` and the constant
`B` of `full-mf-radical-forces-perfect-commutator-bound` are explicit.
