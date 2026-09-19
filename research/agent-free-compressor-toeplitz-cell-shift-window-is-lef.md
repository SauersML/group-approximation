---
rg: 2
id: agent-free-compressor-toeplitz-cell-shift-window-is-lef
kind: claim
title: Every finite Heisenberg-cell shift window has finite models retaining the base center
distinct_from:
  toeplitz-defect-roots-form-independent-heisenberg-cells: that identifies the cells inside the Steinberg group; this proves their abstract shift relation theory has finite local countermodels to root collapse.
  hs-schur-toeplitz-root-defect-collapse: the full claim also contains transverse coefficient-multiplication relations absent from the cell-shift subsystem.
---

Let `H_p` be the order-`p^3` Heisenberg group with generators `P,Q,Z`, and let

```text
L_p=(direct_sum_(n in Z) H_p) semidirect Z,                (CSL1)
```

where the generator `t` of `Z` shifts the coordinates. Write `P_n,Q_n,Z_n`
for the generators in coordinate `n`. Then all relations supplied by
`toeplitz-defect-roots-form-independent-heisenberg-cells`, together with

```text
t P_n t^-1=P_(n+1),
t Q_n t^-1=Q_(n+1),
t Z_n t^-1=Z_(n+1),                                      (CSL2)
```

hold in `L_p`, while `Z_0` is nontrivial.

More strongly, every fixed finite relation window has an exact finite model
which keeps `Z_0` at normalized-HS distance `sqrt(2)` from the identity. For a
window supported in `[-D,D]`, choose `N>2D+1` and use

```text
L_(p,N)=H_p^N semidirect C_N,                              (CSL3)
```

with cyclic coordinate shift. Reduction of indices modulo `N` is injective on
that window, so all products, commutators, and shift conjugacies in the window
are preserved. In the left regular permutation representation of `L_(p,N)`,
the nonidentity element `Z_0` has trace zero and hence

```text
||lambda(Z_0)-I||_2=sqrt(2).                              (CSL4)
```

Equivalently, `L_p` is residually finite by these cyclic-coordinate quotients.
Its group von Neumann algebra is hyperfinite because `L_p` is amenable, giving
the infinite-tensor absorption model anticipated in
`hs-schur-toeplitz-root-defect-collapse`.

Therefore no proof of Toeplitz-root collapse can use only independent
Heisenberg cells, their pairwise commutation, and stable-letter shift. Such a
proof would contradict the exact finite models `(CSL3)--(CSL4)`. A surviving
argument must use a relation from the full coefficient multiplication which
is absent from `L_p`--for example a transverse root relation involving a
non-idempotent coefficient across the one-sided head/tail boundary--and must
show that arbitrary HS microstates authenticate that relation on the same
root-character carrier.

## Attempts

- **Hyperfinite tensor absorption.** This is not merely a heuristic escape:
  `(CSL1)` supplies an exact amenable model with stationary nontrivial centers.
- **Cyclic tensor closure.** On any prescribed depth, choosing a longer cycle
  avoids wraparound inside the inspected window and gives the exact finite
  quotient `(CSL3)`. Thus the boundary error cannot be detected by any fixed
  menu consisting only of cell and shift words.
- **Dimension growth.** The finite models naturally have exponentially growing
  dimension, exactly absorbing the `p^r` cost of `r` active central
  characters. Hyperlinearity permits this growth, so the Heisenberg dimension
  bound alone supplies no contradiction.
