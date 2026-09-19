---
rg: 2
id: bounded-prototype-rows-imply-atomic-morita-return
kind: claim
title: Finitely many losslessly addressed prototype rows imply Atomic Morita Return
distinct_from:
  conjugacy-addressed-opnorm-challenges-are-lossless: that proves literal conjugation preserves one operator-norm discrepancy at arbitrary address length; this packages finitely many such prototype discrepancies into the three returned Leavitt rows on a prescribed spectral atom.
  opnorm-coordinatewise-capacity-diagonal: that chooses a challenge large enough to defeat a frozen coordinate; this needs only one binary cell and lets the address or finite coefficient window vary with the coordinate.
artifacts:
  - research/bounded-prototype-row-compiler-proof.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**ESTABLISHED ABSTRACT COMPILER.** Let `Gamma=<S|R>` have a finite
presentation and finite-order mark `w`.  Suppose there are finitely many
fixed discrepancy words `q_1,...,q_N` in the normal closure of `R` and a
constant `C` with this property.

Every finite-dimensional presentation model retaining a prescribed
nontrivial rounded spectral projection `p_U` admits a coordinate-dependent
address `a`, a coordinate-dependent finite coefficient window, and four
operators in `p_U M_d(C)p_U` whose three binary Leavitt defects are bounded
by

```text
C max_j ||q_j(U)-1||_op.                               (BPR1)
```

Every remotely addressed check is a literal conjugate `a^-1 q_j a`.
Then `(Gamma,w)` has AMR.  Consequently `w` lies in the MF radical, and a
normally generating `w` gives total MF radical.

The address may have unbounded word length and may be selected after seeing
the matrix coordinate.  Literal unitary conjugation is isometric, so the
address creates no word-length loss.  This is the moving-window form of the
atomic return theorem.

