# Referee report (gq-referee-a, proof-gap lens): AF groupoid rings have no finitely generated subring containing Q

**Reviewed:** `af-groupoid-rings-have-no-fg-subring-containing-q` and its route `-proof` (lane gq-deep-adelic-1,
a922d082a), read on origin/main.

**Verdict: PASS for copies of `Q` that contain `1_R`.** A copy whose unit is a proper idempotent is not covered as
written. A three-line addition covers it (§3).

## 1. The setting
- **Convolution is a finite sum.** Only `α` in `K ∩ G^{r(γ)}` contribute. That set is compact, and it is closed and
  discrete because `G` is étale and Hausdorff.
- **`F_c(G,Q)` is a ring.** This holds for arbitrary compactly supported functions, not only continuous ones.
  Associativity is a rearrangement of finite sums, and the unit is `χ_{G^(0)}`.
- **Examples.** Bratteli tail groupoids are AF. So is `Γ ⋉ X` with `Γ` locally finite: a compact set lies in some
  `F × X` with `F` finite, and `⟨F⟩ ⋉ X` is a compact open subgroupoid.

## 2. The proof
- **Step 1.** Finitely many compact supports lie in one compact open `H ⊇ G^(0)`, by the AF hypothesis.
- **Step 2.** `F_H` is a unital subring. Products stay supported on `H` because `H` is a subgroupoid, and
  `χ_{G^(0)}` lies in `F_H`.
- **Step 3.** `H_x = H ∩ s^{-1}(x)` is closed and discrete in the compact `H`, so it is finite.
  - I checked that the left regular formula is multiplicative. Substitute `j = kk'` in the double sum, which gives
    `(f*g)(j)`.
  - The unit acts as the identity. So `π_x` is a unital map into `M_{|H_x|}(Q)`.
- **Step 4.** `fg-q-rings-have-no-matrix-representations` applies.

## 3. A copy of Q whose unit is a proper idempotent `e`
- **A faithful family.** `π_x(f)δ_x = f|_{H_x}`. So the `π_x` are jointly faithful, and some `π_x(e) = E` is nonzero.
- **Reduce to one ring `Z[1/N]`.** The entries of `π_x` on the finitely many generators of `R` lie in a finitely
  generated subring of `Q`. That subring is contained in some `Z[1/N]`.
- **Divisibility.** For every prime `p ∤ N`, the equation `pX = E`, with `X = π_x(1/p)`, puts `E/p` in
  `M(Z[1/N])`.
- **Conclusion.** If an entry `m/N^j` of `E` has `m/(pN^j) ∈ Z[1/N]` for infinitely many primes `p`, then
  `m = 0`. So `E = 0`, a contradiction.
- **Recommendation.** Add this, or state the claim for unital copies only.
