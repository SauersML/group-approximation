# Strict comparison divides the unit over C-space tracial boundaries, part 3: summable local division (2026-09-13)

Lane `ex-tw-rotation-gluing`. Continues parts 1 and 2
(`research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md`,
`research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md`). Not reviewed.

**Outcome.** Theorem E characterizes divisibility of the unit, under strict comparison on a Bauer
simplex, by a local quantitative covering property of the extreme boundary.
- Theorem A of part 1 is its property C case.
- Proposition D of part 2 is its single-precision case.
- It localizes failure to a closed *summable-division locus*. That locus contains no nonempty relatively
  open C-space, so it lies in the C-kernel of the boundary. This settles the open refinement recorded on
  `bauer-strict-comparison-unit-division-is-local`.

## 6. Summable local division

Throughout, `A` is unital, simple, separable, exact and non-elementary, with strict comparison, and
`T(A)` is a nonempty Bauer simplex with extreme boundary `K`.

**Definitions.**
- A *division set* is a tuple `(O, φ, N, δ)`: an open `O ⊆ K`, and a c.p.c. order zero `φ: M_N → A` with
  `λ(1 − φ(1)) < δ` for every `λ ∈ O`, where `0 < δ ≤ 1`. Its *weight* is `ω = (1/N + δ)^{1/2}`.
- A finite family of division sets `(O_i, φ_i, N_i, δ_i)` is *ε-summable* if every `λ ∈ K` has
  `Σ_{i : λ ∈ O_i} ω_i ≤ ε`. It *covers* `Y ⊆ K` if `Y ⊆ ⋃_i O_i`.
- `Y ⊆ K` is *summably divisible* if for every `ε > 0` some ε-summable family covers `Y`.
- The *summable-division locus* `Z_sum(A)` is the set of `λ ∈ K` with no summably divisible closed
  neighbourhood.
- For a compact metrizable `X`, `X_C` is the set of points with no closed neighbourhood that has
  property C. The *C-kernel* `X^{(C,∞)}` is the stable value of the transfinite sequence
  `X^{(0)} = X`, `X^{(α+1)} = (X^{(α)})_C`, with intersections at limits.

**Theorem E.**
- (a) The unit of `A` is tracially `N`-divisible for every `N` iff `K` is summably divisible.
- (b) `Z_sum(A)` is closed, and the unit divides iff `Z_sum(A) = ∅`.
- (c) Every closed `Y ⊆ K` with property C is summably divisible.
- (d) No nonempty relatively open subset of `Z_sum(A)` has a closed neighbourhood in `Z_sum(A)` with
  property C. Hence `Z_sum(A) ⊆ K^{(C,∞)}`. In particular, if the unit does not divide, then `K` contains a
  nonempty closed set in which no point has a closed neighbourhood with property C.

### Proof of (a)

*(⟹).* Given `ε`, take `N ≥ 4/ε²` and `φ: M_N → A` with `τ(1 − φ(1)) < ε²/4` at every trace. Then
`(K, φ, N, ε²/4)` alone is an ε-summable family covering `K`.

*(⟸).* Rerun Section 3 of part 2 with one level per member of an ε'-summable family covering `K`,
where `ε' = ε/14` and `ε` is as in Section 3.
- **No combining needed.** Lemma 2 is not needed: each member is a division set. Take a partition of unity
  `h_i` with `supp h_i ⊆ O_i`.
- **Staircases and bounds.** Lemma 3, (F5) and the bounds (R-up), (R-low) hold per member, with
  `s_i = (1/(4N_i) + δ_i)^{1/2} ≤ ω_i` and `δ_i ≤ ω_i`.
- **Summation.** A member is *active* at `λ` only if `h_i(λ) > 0`, hence `λ ∈ O_i`. So the sums in Steps 5
  and 6 that range over active members satisfy
  ```text
  Σ_{i active at λ} (6 s_i + δ_i + s_i)  ≤  8 Σ_{i : λ ∈ O_i} ω_i  ≤  8ε/14  <  ε/1.75.
  ```
  The inactive terms `8η/s_min` and the cut terms are handled as before, since `η`, `ε'_i` and `ε_i` are
  chosen after the family is fixed.
- **Margins.** The margin in Step 5 stays at least `1 − t − ε ≥ 1/8`.
- **Result.** The final rank lies within `ε < γ` of `t` at every trace, and Step 7 applies. ∎

### Proof of (b)

- **Closed.** If `λ` has a summably divisible closed neighbourhood `Y`, so does every point of `int Y`. So
  the complement of `Z_sum` is open.
- **If the unit divides.** Then `K` is summably divisible by (a), so `Z_sum = ∅`.
- **If `Z_sum = ∅`.** Choose closed summably divisible neighbourhoods whose interiors cover `K`, and keep
  finitely many, `Y_1, …, Y_m`. Given `ε`, take `ε/m`-summable families covering the `Y_j`. Their union
  covers `K`, and at every point its weights sum to at most `m · ε/m = ε`. So `K` is summably divisible and
  (a) applies. ∎

### Proof of (c)

Fix `ε`. Put `ω_k = ε 2^{−k}`, and choose `N_k, δ_k` with `(1/N_k + δ_k)^{1/2} ≤ ω_k`.
1. **Covers.** By Lemma 1, every `y ∈ Y` lies in the open set of a division set at precision `(N_k, δ_k)`.
   The traces on `Y` of these open sets form an open cover `U_k` of `Y`.
2. **Screening.** Property C for `Y` gives disjoint relatively open families `V_k` refining `U_k` with
   `⋃_k V_k` covering `Y`. By compactness finitely many members `V_{k,a}`, `k ≤ L`, cover `Y`.
3. **Closed shrinking.** Shrink to closed `C_{k,a} ⊆ V_{k,a}`, closed in `Y` and hence in `K`, still
   covering `Y`.
4. **Separation.** For fixed `k` the `C_{k,a}` are pairwise disjoint compact sets. So they have pairwise
   disjoint open neighbourhoods `G_{k,a}` in `K`.
5. **Division sets.** Choose a division set `(O, φ, N_k, δ_k)` with `V_{k,a} ⊆ O ∩ Y`. Replace `G_{k,a}` by
   `G_{k,a} ∩ O`, which still contains `C_{k,a}`, and keep `φ`.
6. **Summability.** The resulting division sets cover `Y`. At any `λ ∈ K`, at most one set per level
   contains `λ`, so the weights there sum to at most `Σ_k ω_k ≤ ε`. ∎

**Closed heredity of property C** (used below; elementary). Let `F ⊆ X` be closed, and let `(U_k)` be
open covers of `F`.
- Extend each member to an open set of `X` and add `X ∖ F`. This gives open covers of `X`.
- Apply property C in `X`, restrict the refining families to `F`, and discard the members that refine
  `X ∖ F`. They meet `F` in the empty set, and what remains still covers `F`.

### Proof of (d)

**Step 1: no relative C-neighbourhoods.**
- Suppose `λ ∈ Z := Z_sum(A)` has a closed neighbourhood `F` in `Z` with property C. Put `U = int_Z F`, and
  choose an open `B ∋ λ` in `K` with `cl B ∩ Z ⊆ U`.
- Fix `ε > 0`. By (c) some ε-summable family `𝓕` covers `F`. Put `G = ⋃ 𝓕`.
- The compact set `cl B ∖ G` misses `Z`, because `cl B ∩ Z ⊆ F ⊆ G`. So finitely many closed summably
  divisible neighbourhoods `Y_1, …, Y_m` cover it. Here `m` may depend on `ε`.
- Take `(ε/m)`-summable families covering each `Y_j`. Together with `𝓕` they cover `cl B`, and at every point
  the weights sum to at most `ε + m · ε/m = 2ε`.
- Since `ε` is arbitrary, the closed neighbourhood `cl B` of `λ` is summably divisible, so `λ ∉ Z`.
  Contradiction.

**Step 2: the C-kernel.**
- Let `Z ⊆ X` be closed with `Z_C = Z` (Step 1). A closed C-neighbourhood `N` of `z ∈ Z` in `X` gives the
  closed C-neighbourhood `N ∩ Z` of `z` in `Z` (closed heredity). So `Z ⊆ X_C`.
- By transfinite induction, `Z ⊆ K^{(α)}` for every `α`. ∎

*Order of choices in Step 1.* `m` is chosen after `𝓕`. That is harmless: each `Y_j` is summably
divisible, so its family can be taken `(ε/m)`-summable once `m` is known.

## 7. What a counterexample must do, and model tests

**What a counterexample must do.** Let `A` be exact, with strict comparison, a Bauer simplex, and an
indivisible unit. Then:
- `Z_sum(A) ≠ ∅` is closed and nowhere C in itself;
- for some `ε > 0`, every finite cover of `K` by division sets has a point where the weights sum to more
  than `ε`.

So local divisions at fine precision must live only on sets that no summable screening can arrange, as on
Hilbert cube faces.

**Model tests.**
- *A trivial model fails the hypothesis.* For `C(K)`, every order zero `M_N → C(K)` with `N ≥ 2` is zero, so
  a division set has `ω ≥ 1`, and `K` is not summably divisible, matching (a). `C(K)` is not simple, and
  Lemma 1 is where simplicity enters.
- *A real object satisfies it.* A `Z`-stable algebra with Bauer simplex has `K` as a division set at every
  precision.
