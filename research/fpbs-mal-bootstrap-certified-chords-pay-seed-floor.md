---
rg: 2
id: fpbs-mal-bootstrap-certified-chords-pay-seed-floor
kind: claim
title: A chord graphing over K = <a, bab^-2> whose chord-cell bootstrap closure is conull has unweighted mass at least sigma_b, whatever its label lengths, and generation does not imply bootstrap
distinct_from:
  fpbs-mal-graphing-b-length-weighted-floor: that bounds the b-length weighted mass of every generating graphing; this bounds the unweighted mass, with no length dependence, but only for graphings whose generation is certified by single-chord cell firings.
  fpbs-weakly-bernoulli-fold-seeds-have-density-floor: that is the floor for b-seeds alone (labels in K b K); this transfers it to arbitrary labels of any length through a firing-to-chord charge, and is the input it is applied to.
  fpbs-mal-sprinkle-then-absorb-inert: that kills absorption by infinite-contact steps with bounded crossings for sparse block sprinkles; this kills every seed-plus-local-absorption scheme in which each long chord closes one gap on its own path, for any sprinkle and any lengths.
  fpbs-mal-fold-closure-exactness: that proves the 2-of-3 closure is exact for b-seeds; this shows the chord-cell extension of the closure is not exact (a generating graphing with empty bootstrap closure).
artifacts:
  - experiments/fpbs-chord-bootstrap-2026-09-17/bootstrap_injection.py
  - experiments/fpbs-chord-bootstrap-2026-09-17/bootstrap_injection_out.txt
---

**ESTABLISHED** through `fpbs-mal-bootstrap-certified-chords-pay-seed-floor-proof`.

Let `L = F(a, b)` act p.m.p. on `(X, μ)`, `K = <a, c>`, `c = b a b^{-2}`.
The b-edge at a point `z` is the pair `(z, b z)`. Let `Φ = ⊔ h|_{D_h}` be a
graphing. Fix for each chord instance `x ∈ D_h` one word for `h` (a path).
Its b-letters use the b-edges at points `s_1(x), …, s_r(x)`: the current
point for a letter `b`, and `b^{-1}` of it for a letter `b^{-1}`.

**Bootstrap closure.** For `A_0 ⊆ X`, let `boot_Φ(A_0)` be the least set
containing `A_0` and closed under:
- (T) if two entries of `(w, a w, b w)` are in the set, add the third;
- (C) if `x ∈ D_h` and all but one of the distinct points among
  `s_1(x), …, s_r(x)` are in the set, add the remaining one.

Any word for `h` uses at least `|h|_{K,b}` distinct b-edges, because its
walk in the coset graph joins `Kx` to `Khx`.

Both rules are sound: `boot_Φ(A_0) ⊆ {z : z R' b z}` for
`R' = R_K ∨ b|_{A_0} ∨ Φ`.

**Claim.**
1. **(Charge.)** There is a measurable `A_1` with
   `μ(A_1) ≤ Σ_h μ(D_h)` and `boot_Φ(A_0) ⊆ cl(A_0 ∪ A_1)`, where `cl` is the
   plain 2-of-3 closure (rule (T) only). No freeness is used.
2. **(Floor.)** If `boot_Φ(A_0)` is conull, then
   `μ(A_0) + Σ_h μ(D_h) ≥ σ_b(X)`. On every action weakly contained in a
   Bernoulli shift of `L` this is `≥ 1/80`. It holds for all label lengths and
   paths, with no weight `|h|_{K,b}`.
3. **(Not exact.)** On every free action, the graphing
   `Φ_0 = bab|_X ⊔ bbab|_X` generates, `R_K ∨ Φ_0 = R_L`, since
   `bbab (bab)^{-1} = b`. Yet both labels have `|h|_{K,b} = 2`, so
   `boot_{Φ_0}(∅) = ∅`.

**Reading.**
- Item 2 kills every refutation of `fpbs-mal-bernoulli-single-stage-floor`
  of the form "sparse seeds, then long chords absorbed one at a time". That is,
  each chord closes the last open b-edge on its own path. Such schemes cost
  `≥ σ_b ≥ 1/80` however long, shared or numerous the chords are.
- By Item 3, the survivor P2 (shared-seed long chords) can live only in the gap
  between generation and bootstrap. A counterexample graphing of mass
  `ε < σ_b` must have `boot_Φ(A_0)` non-conull for every `A_0` with
  `μ(A_0) < σ_b − ε`. So it derives a non-null set of b-edges only through
  circuits of several chords, as in Item 3, where `b` appears only as the
  composite `h_2 h_1^{-1}`.
- The same holds at each stage `H_n ≤ H_{n+1}` of `Gamma_mal`, for labels in
  `H_{n+1}`, since `σ_b ≥ 1/80` is uniform in the stage.
