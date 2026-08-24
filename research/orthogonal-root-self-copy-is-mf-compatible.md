---
rg: 2
id: orthogonal-root-self-copy-is-mf-compatible
kind: claim
title: Orthogonal root self-copy and normal generation are compatible with MF
distinct_from:
  bare-self-copy-mf-calibration: that gives a finitely presented operator-MF self-compression group whose exact finite-dimensional representations kill a marked commutator; this gives locally finite root-calculus examples with commuting orthogonal copies and root normal generation.
  binary-leavitt-heisenberg-is-orthogonal-central-self-copy: that supplies the exact Leavitt three-root self-copy and proves that subsystem locally finite; this adds the finitary elementary-group calibration for the normal-generation part of the slogan.
artifacts:
  - research/orthogonal-root-self-copy-mf-calibration-proof.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**ESTABLISHED CALIBRATION.** For a finite field `F_q`, let

```text
G=E_fin(F_q)=union_n E_n(F_q)
```

under the standard stabilization maps.  Then:

1. `G` is locally finite and hence MF;
2. it has the full Steinberg addition, multiplication and off-root
   commutation calculus;
3. a partition of the countable coordinate set into two infinite subsets
   gives two commuting block subgroups, each isomorphic to `G`;
4. every nontrivial elementary root normally generates `G`.

Together with the locally finite binary-Leavitt Heisenberg self-copy, this
shows that

```text
orthogonal self-copy + root commutator calculus + normal generation
```

is not a valid non-MF criterion.  The missing datum must be a matricial
return to the same nonzero atom, a rank-product cycle, an integral index, or
another non-scalable finite-coordinate mechanism.
