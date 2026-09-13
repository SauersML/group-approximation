---
rg: 2
id: kazhdan-reps-without-fd-subreps-have-linear-subspace-boundary
kind: claim
title: In a unitary representation of a Kazhdan group with no finite-dimensional subrepresentation, every finite-dimensional subspace moves by a fixed fraction of its dimension
distinct_from:
  kazhdan-rank-rounding-fails-over-every-field: that shows genuine non-unitary models of a Kazhdan group over every field carry subspaces of every size with bounded boundary; this is the unitary inequality, for representations with no finite-dimensional subrepresentation, where such subspaces cannot exist.
  kazhdan-group-rank-models-admit-no-expander-decomposition: that is the failure of dimension expansion over F_2; this is its unitary counterpart, where expansion holds on every finite-dimensional subspace of an infinite-dimensional representation.
---

**ESTABLISHED** (`kazhdan-linear-subspace-boundary-proof`). Unreviewed.

Let `G` be a group with a Kazhdan pair `(Q, kappa)`, `Q` finite. Let `pi : G -> U(H)` be a unitary
representation with **no nonzero finite-dimensional subrepresentation**. For a finite-dimensional
subspace `W <= H` and `q` in `G` put

```text
e_q(W) = dim W - dim(W n pi(q) W).
```

Then

```text
max_(q in Q) e_q(W) >= kappa^2 dim W / 2.                              (LB1)
```

**Remarks.**
- For an irreducible finite-dimensional `pi` of dimension `N`, the same argument applied to
  `P_W - (dim W / N) I` gives `max_q e_q(W) >= kappa^2 dim W / 4` when `dim W <= N/2`. That is the
  dimension-expander property of irreducible unitary representations of Kazhdan groups
  (Lubotzky--Zelmanov, recalled and not re-read here; Remark 2.2 of
  `research/artifacts/kazhdan-rank-rounding-counterexample-2026-09-12.md`).
- `(LB1)` is the infinite-dimensional form with no finite-dimensional part to subtract. It needs
  the Hilbert structure: over any field, `EL_3(Z[t])` has genuine non-unitary representations with
  subspaces of every dimension and boundary at most one
  (`kazhdan-rank-rounding-fails-over-every-field`).
- **Use.** A unitary tuple that agrees with `pi(q)` on a subspace of `W` of codimension at most `B`,
  for every `q` in `Q`, forces `dim W <= 2B / kappa^2`. So bounded-boundary truncations of such a
  `pi` have bounded dimension. The consumer is `deligne-sector-truncations-have-bounded-dimension`.
