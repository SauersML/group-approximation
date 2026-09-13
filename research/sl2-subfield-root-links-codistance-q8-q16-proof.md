---
rg: 2
id: sl2-subfield-root-links-codistance-q8-q16-proof
kind: route
title: Exact closed-walk counts at one vertex of a vertex-transitive coset graph bound its second singular value
target: sl2-subfield-root-links-codistance-q8-q16
requires: [coset-graph-singular-values-bound-fixed-space-angles]
artifacts: [experiments/sl2-root-triangle-kazhdan/sl2link.py, experiments/sl2-root-triangle-kazhdan/run1.out, experiments/sl2-root-triangle-kazhdan/run2.out]
---

**The trace inequality.** Let `M` be the biadjacency matrix of `Γ_s`, with side-1 vertices `SL_2(F)/u(k)`,
and put `T = MM^T / q^2`.
- The eigenvalues of `T` are `σ_1^2 = 1 >= σ_2^2 >= … >= 0`, one per side-1 vertex.
- `(T^m)_{vv} = W_{2m}(v) / q^{2m}`, where `W_{2m}(v)` counts closed walks of length `2m` at `v`.
- `SL_2(F)` acts transitively on side 1 by graph automorphisms, so `W_{2m}(v) = W_{2m}` for all `v`.

Therefore

```text
σ_2^{2m}  <=  Σ_{i>=2} σ_i^{2m}  =  tr(T^m) - 1  =  n W_{2m} / q^{2m} - 1 .
```

For `θ = a/b`, the integer inequality `(n W_{2m} - q^{2m}) b^{2m} < a^{2m} q^{2m}` certifies `σ_2 < θ`. If
`Γ_s` were disconnected, `tr(T^m) - 1 >= 1`, so a certificate with `θ < 1` also certifies connectivity.

**The computation** (`sl2link.py`, run on MSI with Sage 10.7's Python; outputs `run1.out`, `run2.out`).
1. **The field.** `F_{2^n}` is built with log tables, from the first polynomial whose root has order
   `2^n - 1`. That is `x^6 + x + 1` for `F_64` and `x^8 + x^4 + x^3 + x^2 + 1` for `F_256`. `k` is
   computed as `{a : a^q = a}`.
2. **The graph.** Side-1 vertices are pairs `(v, t mod k)`. Here `v = ge_1 ∈ F^2 \ 0` and
   `ge_2 = w_0(v) + t v`, where `w_0(v)` is a fixed solution of `det(v, w) = 1`. Side-2 vertices are
   `(ge_2, t' mod sk)` in the same way. Each `g` gives one edge.
3. **Assertions.** Every edge has `det = 1`. Both sides have all degrees equal to `q`. The biadjacency
   matrix is 0/1.
4. **Calibration.** With `L = L' = F_q`, the same builder gives the root links of `SL_2(8)` and `SL_2(16)`.
   It returns girth 6 and `σ_2 = 0.353553, 0.250000`, the exact values of
   `sl2-opposite-root-subgroups-codistance-inverse-sqrt-q`.
5. **Walk counts.** `W_{2m}` is the `(0,0)` entry after `m` rounds of `M^T` then `M` applied to `δ_0`. The
   counts are done modulo 57-bit primes, enough that the product exceeds `2^{bits(q^{2m} n)}`, and
   reconstructed by CRT. Sums of at most `q` residues below `2^57` never overflow `int64`.
6. **Certificate check.** Each reconstructed `W` is checked against `W <= q^{2m}` and
   `n W >= q^{2m}`.

**Results.** The inequality holds with `θ = 3/4` for `q = 8` from `2m = 56` (`s = g`) and `2m = 48`
(`s = g^3`). It holds with `θ = 7/8` for `q = 16` from `2m = 18` for both classes. It holds at every
larger `2m` computed, as it must.

**Trust boundary.**
- The certificate relies on the correctness of the builder and of scipy's integer sparse products.
- The Lanczos values and BFS girth are reported as numerics and exact combinatorics, respectively. The
  theorem uses only the certificate and connectivity. ∎
