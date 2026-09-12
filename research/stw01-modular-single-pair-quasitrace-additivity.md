---
rg: 2
id: stw01-modular-single-pair-quasitrace-additivity
kind: claim
title: Every bounded 2-quasitrace on C*(PSL_2(Z)) is additive on the one pair e_1 p e_1, e_1 p e_2 p e_1
distinct_from:
  stw01-modular-group-algebra-quasitraces-are-traces: that asks every bounded 2-quasitrace on C*(PSL_2(Z)) to be linear; this asks additivity on one fixed pair of positive elements, which already forces Problem I.
  stw99-problem-i-quasitraces-are-traces: that is Kaplansky's question for every C*-algebra; this is additivity of one explicit pair in one algebra, equivalent to it.
  stw01-three-projection-algebra-quasitraces-are-traces: that is linearity on C^2*C^2*C^2; this is additivity on one pair in its quotient C^3*C^2.
artifacts:
  - research/artifacts/stw01-modular-single-pair-test-2026-09-12.md
---

In `Q = C^3 * C^2 = C*(PSL_2(Z))`, the universal unital C*-algebra of a partition of
unity `e_1, e_2, e_3` and one projection `p`, put `h = e_1 p e_1` and
`k = e_1 p e_2 p e_1`. Then every bounded 2-quasitrace `sigma` on `Q` satisfies

```text
sigma(h + k) = sigma(h) + sigma(k).
```

**This single-pair statement is equivalent to STW Problem I.** The implication into the
root is `stw01-problem-i-via-modular-single-pair`. The proof is in
`research/artifacts/stw01-modular-single-pair-test-2026-09-12.md`, Section 2. It tunes
an affine rescaling `a = (1/2) 1 + eps y` by the intermediate value theorem, so that
the three-block dilation constant equals `eps beta`. That removes both the functional
calculus `g` and the scalar `t` from the witness shape on
`stw01-modular-group-algebra-quasitraces-are-traces`. The converse is trivial.

**Where the difficulty sits.**
- `C*(h, k)` is not exact, since it surjects onto `Q`
  (`stw01-modular-test-pair-generates-non-exact-algebra`). So no exactness argument
  applies to any algebra containing the pair.
- `sigma` is already a trace on `C*(e_1, p)`, which contains `h` and `h - h^2 = k + e_1 p e_3 p e_1`.
- The whole question is whether the defect can sit in the split of `h - h^2` into the
  `e_2` and `e_3` parts.

## Attempts

- **Exactness of an ambient subalgebra (Haagerup).** Dead: the pair generates a
  non-exact algebra.
- **Traces on the two-projection subalgebras `C*(e_j, p)`.** `sigma` is linear on each,
  and the pair `(h, k + e_1 p e_3 p e_1)` is additive. But `k` lies in no
  two-projection subalgebra, and `C*(e_1, e_2, p) = Q`.
- **Residual finite-dimensionality (Exel–Loring).** A non-linear quasitrace is not a
  weak* limit of finite-dimensional traces, so RFD structure alone gives nothing.
- **The `e_2 <-> e_3` symmetry.** It gives the equally good test pair
  `(h, e_1 p e_3 p e_1)`, and no relation between the two defects without linearity.
