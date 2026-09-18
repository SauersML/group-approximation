---
rg: 2
id: gapped-bernoulli-kernels-vanish-via-boundary-continuity
kind: route
title: Continuity of the diagonal of a gapped kernel projection carries delocalization to the tree boundary, faithfulness of the expectation kills the boundary restriction, and Theorem D kills the ranks
target: delocalized-gapped-bernoulli-kernels-vanish-at-marked-expanders
requires:
  - hls-ghost-class-never-lifts-to-the-bernoulli-full-shift
  - bernoulli-assembly-injective-beyond-the-host
  - bernoulli-bc-splits-into-host-and-cylinder-comparison
  - split-quotients-give-exact-reduced-crossed-products
artifacts:
  - research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md
---

The notation is that of `delocalized-gapped-bernoulli-kernels-vanish-at-marked-expanders`. Short names:
- **D** = `hls-ghost-class-never-lifts-to-the-bernoulli-full-shift` (Theorem D);
- **RF** = `bernoulli-assembly-injective-beyond-the-host`;
- **CC** = `bernoulli-bc-splits-into-host-and-cylinder-comparison`;
- **L1.1** = Lemma 1.1 of `research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md`.

## 0. Conventions

- `G` acts on `X = Λ^G` by `(g·x)(v) = x(g^(-1) v)`, so `g·1_A = 1_(gA)`.
- For `z ∈ X`, the regular representation `π_z` of `M_k(C(X) ⋊_r G)` acts on `l^2(G) ⊗ C^k` by:
  - `π_z(f) δ_h = f(h·z) δ_h`;
  - `π_z(u_g) δ_h = δ_(gh)`.

  Covariance holds: `π_z(u_g f u_g^*) δ_h = f(g^(-1) h·z) δ_h = π_z(g·f) δ_h`.
- For `b = Σ_g f_g u_g` in the algebraic crossed product, the diagonal block is `⟨π_z(b) δ_h, δ_h⟩ = f_e(h·z) = E(b)(h·z)`.
  By continuity this holds for every `b`.
- If `z` has trivial stabilizer, then for positive `b`:
  - `Tr π_z(b) = Σ_(w ∈ G·z) tr E(b)(w)`, with values in `[0, ∞]`;
  - `sup_h tr⟨π_z(b) δ_h, δ_h⟩ = sup_(w ∈ G·z) tr E(b)(w)`.
- `π_z` is unitarily equivalent to `Ind_({e})^G(ev_z)`, the representation used by RF item 1.
- Functional calculus commutes with *-homomorphisms. So `P_z = π_z(P) = 1_({0})(a_z)`, and `spec(a_z) ⊆ spec(a)` keeps
  the gap. In particular `a_z` is invertible iff `P_z = 0`.

## 1. Boundary points are far-marker limits

**Lemma 1.** Let `z ∈ ∂Y \ {0}` and `g_i·x_(n_i) -> z`. Then `n_i -> ∞`.

*Proof.* Otherwise some subsequence converges to `z` with `n_i` not tending to `∞`. L1.1 (a) then gives
`z ∈ U = ∪_n G·x_n`, contradicting `z ∈ ∂Y = Ŷ \ U`. ∎

**Lemma 1'.** Let `w_n ∈ G·x_n` for `n` in an infinite set `S`, and let `z` be a limit point of `(w_n)_(n ∈ S)`. Then
`z ∈ ∂Y`.

*Proof.* `z ∈ Ŷ`. Suppose `z = g·x_m ∈ U`.
- By L1.1 (c), `x_m` is isolated in `Ŷ`, so `g·x_m` is isolated in `Ŷ`.
- So `w_n = g·x_m` for infinitely many `n ∈ S`.
- `|supp w_n| = |A_n|` and the sizes are strictly increasing. So `|A_n| = |A_m|` holds for at most one `n`, a
  contradiction. ∎

## 2. Proof of Theorem K (b)

Let `z ∈ ∂Y \ {0}`.
- `X` is metrizable and `z ∈ closure(U)`, so `z = lim g_i·x_(n_i)`. By Lemma 1, `n_i -> ∞`.
- `tr E(P)` is continuous, since `E(P) ∈ M_k(C(X))`.
- Therefore `tr E(P)(z) = lim_i tr E(P)(g_i·x_(n_i)) <= lim_i sup_(w ∈ G·x_(n_i)) tr E(P)(w) = 0`.

By §0 the supremum is `sup_h tr⟨P_(x_n) δ_h, δ_h⟩`. ∎

## 3. Proof of Theorem K (a)

1. **Zero at the fixed point.** `π_0(P) = 1_({0})(a_0 ⊗ 1) = 0`, because `a_0 ∈ M_k(C*_r G)` is invertible. Here `π_0`
   is `ev_0 ⋊ G` followed by the regular representation. So `tr E(P)(0) = 0`, and `tr E(P)` vanishes on all of `∂Y`.
2. **The boundary restriction vanishes.**
   - `∂Y` is closed and invariant (L1.1 (c)). Let `res_∂ : M_k(C(X) ⋊_r G) -> M_k(C(∂Y) ⋊_r G)` be induced by
     restriction.
   - `Q = res_∂(P)` is a projection with `E_∂(Q) = E(P)|_(∂Y)`, a positive matrix function with zero trace, hence `0`.
   - The canonical expectation of a reduced crossed product is faithful, so `E_∂(Q*Q) = E_∂(Q) = 0` gives `Q = 0`.
3. **`P` lies in the ideal.**
   - `ev_0 : C(X) -> C` is equivariant, and the constants give an equivariant *-splitting `s : C -> C(X)`.
   - `id - s∘ev_0` is a difference of two equivariant completely positive maps with range in `C_0(X^0)`. It extends to
     `(id - s∘ev_0) ⋊_r G` on the reduced crossed product. This is the splitting mechanism of
     `split-quotients-give-exact-reduced-crossed-products`.
   - Applied to `P` it gives `P - (s ⋊ G)((ev_0 ⋊ G)(P)) = P`, because `(ev_0 ⋊ G)(P) = 1_({0})(a_0) = 0`.
   - Its range lies in the closure of `M_k(C_c(G, C_0(X^0)))`, which is `M_k(C_0(X^0) ⋊_r G)`. So
     `P ∈ M_k(C_0(X^0) ⋊_r G)`, and `y = [P] ∈ K_0(C_0(X^0) ⋊_r G)`.
4. **`y` vanishes on the boundary.**
   - Reduced crossed products preserve injections, so `C_0(∂Y \ {0}) ⋊_r G ⊆ C(∂Y) ⋊_r G`.
   - The restriction `C_0(X^0) ⋊_r G -> C_0(∂Y \ {0}) ⋊_r G`, composed with this inclusion, is `res_∂` on the ideal. By
     step 2 it sends `P` to `0`.
   - So `y|_(∂Y) = 0` in `K_0(C_0(∂Y \ {0}) ⋊_r G)`.
5. **Ranks.**
   - By RF item 1, `π_(x_n)` maps `C_0(X^0) ⋊_r G` into the compact operators, and `r_(x_n)(y) = rank P_(x_n)`.
   - Theorem D gives `r_(x_n)(y) = 0` for all large `n`. So `P_(x_n) = 0`, and `a_(x_n)` is invertible (§0). ∎

## 4. Proof of Theorem K (c)

**Uniform localization.**
- Suppose the first bullet fails. Then there is an infinite `S' ⊆ S` with `sup_(w ∈ G·x_n) tr E(P)(w) -> 0` along `S'`.
- The subfamily `(A_n)_(n ∈ S')` satisfies (M): each condition is inherited by subsequences. Its boundary `∂Y_(S')` is
  defined from `x_n`, `n ∈ S'`.
- Theorem D and L1.1 hold for this subfamily, because their hypotheses are exactly (M).
- Parts (b) and (a) for the subfamily give `ker a_(x_n) = 0` for large `n ∈ S'`. That contradicts `S' ⊆ S`.

**A boundary point carries the mass.**
- For large `n ∈ S` pick `w_n ∈ G·x_n` with `tr E(P)(w_n) >= ε`, and let `z` be a limit point.
- By Lemma 1', `z ∈ ∂Y`.
- By continuity, `tr E(P)(z) >= ε`. By §3 step 1, `tr E(P)(0) = 0`, so `z ≠ 0`.
- So `res_∂(P) ≠ 0`, since its expectation is nonzero at `z`. ∎

## 5. Proposition R and why the recipe is dead

**Setting.** Take `Λ = Z/p`, and let `μ` be the uniform Bernoulli measure, the Haar measure of `(Z/p)^G`. The Haar trace
of `C*_r(F_p wr_G G) = C(X) ⋊_r G` is `τ(b) = ∫_X tr E(b) dμ`.

**Isolated clusters.** For `z ∈ X`, let `C(z)` be the set of pairs `(n, g)` with `e ∈ gA_n` and
`z|_(gN_n) = (g·x_n)|_(gN_n)`. Call `gA_n` an isolated cluster of `z` when the second condition holds.
- The recipe hypothesis says that `P_z` is the orthogonal projection onto the span of the vectors
  `ξ_(n,g) = |A_n|^(-1/2) Σ_(h^(-1) ∈ gA_n) δ_h ⊗ v`.
- The span runs over the isolated clusters `gA_n` of `z`, and `v ∈ C^k` is a fixed unit vector.
- By §0 the diagonal at `δ_h` sees the configuration `h·z`, whose clusters are `hgA_n`. They contain `e` iff
  `h^(-1) ∈ gA_n`.

**Step R1: clusters are disjoint.** Let `(n, g), (m, g') ∈ C(z)`.
- `A_n` is the vertex set of a connected graph isometrically embedded in the Cayley graph. So `gA_n` is connected in the
  Cayley graph.
- `z` is nonzero on `gA_n` and zero on `gN_n \ gA_n`, which contains every Cayley neighbour of `gA_n` outside it. So
  `gA_n` is the connected component of `supp z` containing `e`.
- The same holds for `g'A_m`. Hence `gA_n = g'A_m`.
- Strictly increasing sizes give `n = m`. L1.1 (b) makes the stabilizer of `A_n` trivial, so `g = g'`.
- Consequences:
  - the vectors `1_(gA_n)` over all such pairs have disjoint supports;
  - the diagonal at `δ_e` is `tr E(P)(z) = Σ_((n, g) ∈ C(z)) |A_n|^(-1)`, with at most one nonzero term.

**Step R2: the trace.**
- The event `z|_(gN_n) = (g·x_n)|_(gN_n)` has `μ`-measure `p^(-|N_n|)`.
- There are exactly `|A_n|` elements `g` with `e ∈ gA_n`, namely `g ∈ A_n^(-1)`.
- By monotone convergence,
  `τ(P) = Σ_n Σ_(g ∈ A_n^(-1)) |A_n|^(-1) p^(-|N_n|) = Σ_n p^(-|N_n|)`.
- The series converges because `|N_n| >= |A_n| >= n`.

**Step R3: outside `Z[1/p]`.**
- Mark only a subsequence with `|N_(n_(j+1))| >= |N_(n_j)| + 2`. (M) is preserved.
- The base-`p` digits of `Σ_j p^(-|N_(n_j)|)` are `0` or `1`, with infinitely many `1`s and never two consecutive `1`s.
- This expansion does not terminate and does not end in a tail of `(p-1)`s (for `p = 2` the gaps prevent this). So it is
  the unique expansion of a number outside `Z[1/p]`.
- CC item 7 would refute surjectivity of reduced assembly for `G` or for `T_r`, hence for `F_p wr_G G`.

**Step R4: the hypothesis is unsatisfiable.**
- Take `w = h·x_n = 1_(hA_n)`.
  - By R1, `C(w)` contains at most the pair `(n, h)`, and it does contain it when `e ∈ hA_n`. So
    `tr E(P)(w) ∈ {0, 1/|A_n|}`, and the supremum over `G·x_n` is `1/|A_n| -> 0`.
  - `P_(x_n)` has rank `1`: the only isolated cluster of `x_n` is `A_n`.
- At `z = 0`, `C(0) = ∅`, so `P_0 = 0`. Since `a` is gapped, `a_0` is invertible.
- Theorem K (b) and then (a) give `P_(x_n) = 0` for large `n`, a contradiction.
- So no gapped operator has the cluster kernel. The recipe dies at its only unproved step, the existence of a gapped
  operator with that kernel. The trace computation R2--R3 was sound. ∎

**Remark (how the obvious operators fail, context only).** Take the induced Laplacian on `supp z` plus a local penalty
for deviations from the marked shapes.
- A cluster that differs from `g·x_n` at `O(1)` sites has a normalized constant vector with Rayleigh quotient
  `O(1)/|A_n|`.
- So nonzero spectrum accumulates at `0`, and no gap survives.
- This is the dilution mechanism noted informally in the Attempts of `hls-ghost-class-lifts-to-the-bernoulli-full-shift`.
  Theorem K makes the failure independent of the operator chosen.

## 6. Calibration

- **HLS subshift.** Over `C(Ŷ) ⋊_r G`, the HLS kernel projection has exactly the diagonal and rank profile of step R4,
  with `a_0` invertible (context, `hls-ghost-projection-breaks-k-exactness`). So the `Ŷ`-analogue of Theorem K is false.
  - In the proof above, the full shift enters only through Theorem D in §3 step 5.
  - Steps 1--4 go through verbatim over `Ŷ`.
  - The HLS class violates the `Ŷ`-analogue of Theorem D.
  - This is the expected sharp failure, not a contradiction.
- **One-site cylinder.** `P = 1_(C_({e},1))` over `Λ = {0,1}`.
  - `P_(x_n)` is the projection onto `l^2(A_n)`, of rank `|A_n|`, with diagonal `1`.
  - Mass `1` appears at every boundary configuration with `z(e) = 1`, as (c) requires.
