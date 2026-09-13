---
rg: 2
id: leavitt-toeplitz-commutator-is-a-v-conjugate-level-relation
kind: claim
title: The Toeplitz commutator relation in the Leavitt unit group is a Thompson V conjugate of a level Steinberg relation
distinct_from:
  natural-compressor-extension-fails-at-toeplitz-commutator: that shows one specific finitary assignment is forced to fail the Toeplitz commutator by a transvection; this shows the relation itself lies in a finite subgroup conjugate into the level group, so the failure belongs to the assignment.
  natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter: that measures the Fock quantization defect of the natural compressor assignment; this is a statement about the relation in the group, independent of any model.
  toeplitz-coefficient-factoring-kills-leavitt-el3-rank-models: that concerns the value at x_12(1 − s0 t0) factoring through a directly finite coefficient ring; this concerns the commutator [x_12(t0), x_23(s0)] = x_13(1).
artifacts:
  - research/artifacts/hnn-intertwiner-cocycle-on-thompson-v-2026-09-12.md
---

**OPEN** (proof: Section 5 of the linked artifact; held open pending re-derivation by `w3-vf-linear`).

**Statement.** Let `K` be a field and `R = L_K(1,2)`, and identify `M_3(R) = R` through the code `(0, 10, 11)`.
Let `w ∈ V` be the prefix replacement `00 -> 0`, `01 -> 101`, `10 -> 100`, `11 -> 11`. Then:
- `x_12(t0) = 1 + s_0 t_100 = w (1 + s_00 t_10) w^(−1)`;
- `x_23(s0) = 1 + s_100 t_11 = w (1 + s_10 t_11) w^(−1)`;
- `x_13(1) = 1 + s_0 t_11 = w (1 + s_00 t_11) w^(−1)`.

So `[x_12(t0), x_23(s0)] = x_13(1)` is the `w`-conjugate of `[1 + e_(00,10), 1 + e_(10,11)] = 1 + e_(00,11)` in
`GL_4(K)`.
- The three elements generate a conjugate of `UT_3(F_p)`: order 27 for `K = F_3` (54 with `z = −1`), and `D_8` for
  `K = F_2`.

**Consequences.**
- **No obstruction.** The relation cannot by itself force `rk(1 − [z]) = 0` in characteristic three. It holds in
  a finite subgroup containing `z`, which has anti-central models such as `σ_reg ∘ Ad(w^(−1))`.
- **Candidate (b).** An extension that assigns the root elements `X_w σ_reg(·) X_w^(−1)` satisfies it exactly.
