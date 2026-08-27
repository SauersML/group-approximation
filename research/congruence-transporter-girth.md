---
rg: 2
id: congruence-transporter-girth
kind: claim
title: Kernel transporters of the marked pair need logarithmic word length in congruence quotients
distinct_from:
  marked-double-coset-infinite-degree: that computes an exact infinite index in the infinite group; this bounds word lengths in finite congruence quotients — a growth statement, not an index computation.
  finite-quotient-blindness: that implies kernel transporters of the marked pair exist in every finite quotient (the collapse); this says that in the congruence family they are necessarily long, so the collapse has logarithmic latency relative to any fixed window.
  compressor-coset-two-point-exact: that separates the compressor coset exactly, where no kernel transporter exists at all; this measures the marked pair, where kernel transporters must exist, by their minimal length.
  pair-constraint-graph-criterion: that is the general conversion of two-point label data into cycle conditions with a girth-type necessary condition; this is the Kun--Thom-specific arithmetic input which that condition consumes.
---

Let `Γ = EL_r(R_+) < G = EL_r(R) ⋊ SL_d(ℤ)` be the Kun--Thom Theorem E pair,
`h = e_12((x_1⋯x_d)^{-1})` the marked element, `p = Γ`, `q = hΓ`, and

```text
π_M : G → Q_M = EL_r(F_q[(ℤ/M)^d]) ⋊ SL_d(ℤ/M)
```

the congruence quotient of `compressor-coset-two-point-exact`.  For a finite
`F ⊆ G` let `C = C(F) ≥ 2` bound, over all letters `g ∈ F ∪ F^{-1}`, both
the ℓ¹ operator norm of the `SL_d(ℤ)`-component and the maximal ℓ¹-norm of
an exponent vector occurring in the Laurent-polynomial entries of the
elementary component.  Then:

1. **Kernel transporters exist at every level.**  The set
   `ker π_M ∩ hΓ` is nonempty — explicitly it contains
   `e_12\big((x_1⋯x_d)^{-1} − (x_1⋯x_d)^{M-1}\big)` — and does not contain
   `1`, since `h ∉ Γ`.

2. **They are logarithmically long.**  Every `F`-word (any signs, any
   spelling) of length `k` whose value is a **nontrivial** element of
   `ker π_M` satisfies

   ```text
   k ≥ log_C(M/2) − 1.
   ```

   In particular every `F`-word valued in `ker π_M ∩ hΓ` has length at
   least `log_C(M/2) − 1`, which tends to infinity with `M`.

3. **Congruence models pass the necessary girth condition.**  Combining
   with item 3 of `pair-constraint-graph-criterion`: for every window `F`
   and precision `ε`, once `M ≥ 2·C(F)^{1/ε + 2}` the exact regular model
   `A = Q_M` has no slot-admissible kernel-transporter word of length
   `≤ 1/ε`, so the deletion bound rejects nothing at that precision.  What
   the girth does **not** provide is the deleted set itself: cutting the
   walks of the long transporters, which exist at every level by item 1, is
   exactly `marked-pair-cut-problem`, and it is all that separates the
   congruence models from two-point data for the marked pair.

The two constants are honest about where the difficulty sits: visibility of
the marked coset in `Q_M` fails immediately (`h̄ ∈ Γ̄` at every level, by
one application of normality), yet certifying the failure inside the model
costs `log M` letters.  The window sees the collapse only through words too
long to fit, and the approximation question becomes a race between the
window's word-length budget `1/ε` and the congruence depth `M`.
