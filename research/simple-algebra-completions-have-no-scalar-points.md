---
rg: 2
id: simple-algebra-completions-have-no-scalar-points
kind: claim
title: No simple algebra carries the Pauli scalar point property on any closed set of traces, and its order zero division capacity is positive
distinct_from:
  pauli-tower-bundle-has-scalar-point-property: that proves the scalar point property for a non-simple C(X)-algebra; this shows that no simple non-elementary algebra has it over any closed set of traces.
  bauer-strict-comparison-unit-divides-iff-atomless-element: that characterizes unit division by heavy eigenvalues under strict comparison; this shows, with no comparison, that the heavy-eigenvalue threshold of a simple algebra is strictly below 1 and is bounded by its division capacity.
---

**Setting.** `A` is unital, simple, separable and non-elementary, `K ⊆ T(A)` is a nonempty
closed set of tracial states, and `M` is a completion of `A` over `K` (uniform tracial
completion, or strict closure when `K` is the extreme boundary of a Bauer simplex). For
`τ ∈ T(A)`, `π_τ` is the GNS representation and `Var_τ(h) = τ(h²) − τ(h)²` for self-adjoint `h`.

**Theorem.**
1. **No scalar points.** If `h = h* ∈ A` is not a scalar, then `π_τ(h) ∉ C·1` for every
   `τ ∈ T(A)`, and `min_{τ∈K} Var_τ(h) > 0`.
2. **No vanishing pieces.** A nonzero positive `a ∈ A` has `τ(a) > 0` for every `τ ∈ T(A)`, and
   `min_{τ∈K} τ(a) > 0`. So `π_τ(a) ≠ 0` for every `τ`.
3. **Positive capacity.** `cap_K(A) = sup_φ min_{τ∈K} τ(φ(1))`, over c.p.c. order zero
   `φ: M_2 → A`, is strictly positive.
4. **Threshold bound.** Say `A` is `ε_0`-rigid over `K` if every self-adjoint `h ∈ A` has some
   `τ ∈ K` at which `π_τ(h)` has an eigenprojection of trace `≥ ε_0`. Then `ε_0 < 1`, and if
   `ε_0 > 1/2` also `cap_K(A) ≤ 1 − ε_0`.

**Consequence for the Pauli tower obstruction.** Its three strongest forms are the scalar point
property (`pauli-tower-bundle-has-scalar-point-property`, rigidity at `ε_0 = 1`), vanishing of one
of two orthogonal positive elements in some fibre, and capacity `0`
(`pauli-tower-bundle-has-no-uniform-order-zero-m2`). None of them survives on the completion of a
simple algebra over any closed trace set, since they already fail on elements of `A`. A simple
algebra can carry the obstruction only quantitatively: `ε_0`-rigidity with `ε_0 < 1`, or capacity
below `1` (indivisibility of the unit over `K`). Rigidity forces indivisibility with no comparison:
the element of the (i) ⟹ (ii) step of `bauer-strict-comparison-unit-divides-iff-atomless-element`
has all atoms `≤ max(1/N, defect)`, so `ε_0`-rigidity over `K` rules out order zero `M_N` with
`N > 1/ε_0` and defect below `ε_0` on `K`.

**Model tests.**
- The Pauli algebra (non-simple) has point traces with nonzero trace-kernel ideals, so part 1
  fails for it, as Theorem A of the Pauli tower requires.
- `M_{2^∞}` (simple, one trace) satisfies parts 1–3, with capacity `1`.

Proof: route `simple-algebra-completions-have-no-scalar-points-proof`. Unreviewed.
