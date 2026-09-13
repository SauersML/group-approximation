# Rips complexes of l^1 products of trees are contractible at large scale (z4-05-raag-rips, 2026-09-13)

Status: complete argument, UNREVIEWED. It verifies the hypotheses of Zaremsky's contractibility criterion
(arXiv:2410.11993, Theorem 3.1) for l^1 products of trees. The only literature input beyond standard
topology is that criterion.

## 0. Statement

**Theorem.** Let `T_1, …, T_k` (`k ≥ 1`) be simplicial trees with edges of length 1 and uniformly bounded
vertex degrees. Let `X = V(T_1) × ⋯ × V(T_k)` with `d_1(x,y) = Σ_i d_{T_i}(x_i, y_i)`. Then `VR_t(X)` is
contractible for every integer `t ≥ k(k+1) − 1`.

**Corollary (RAAGs).** If `Γ` is complete multipartite with parts of sizes `n_1, …, n_k`, then
`A_Γ = F_{n_1} × ⋯ × F_{n_k}`. Its standard word metric is the l^1 product of the Cayley trees (regular of degree
`2n_i`; the line when `n_i = 1`), so `R_t(A_Γ, V(Γ))` is contractible for `t ≥ k(k+1) − 1`, where `k` is the
dimension of `A_Γ`. Examples: `F_2 × F_2 × F_2` (`t ≥ 11`), `Z^2 × F_2` (`K_4` minus an edge, `t ≥ 11`), and
`Z^n` (reproving Zaremsky's bound `t ≥ n^2 + n − 1`).

## 1. The criterion being verified

Zaremsky, *Contractible Vietoris-Rips complexes of Z^n*, arXiv:2410.11993 (v2, Proc. AMS), as rendered on arXiv:
- Property (*): "All distances in X are integers, and for all t ∈ ℕ there exists n_t ∈ ℕ such that |S| ≤ n_t
  for all S ⊆ X with diam(S) = t."
- Theorem 3.1: "Let (X,d) be a metric space satisfying (*). Fix t₀, and suppose that for all t>t₀ there exists
  r_t<t such that every S⊆X with diam(S)=t lies in some ball of radius r_t. Assume moreover that for some such
  ball, its center lies within t of the center of any other such ball. Then VR_{t₀}(X) is contractible."
  Balls are centred at points of `X`. The hypothesis says: with `Y(S) = {y ∈ X : d(y,s) ≤ r_t ∀ s ∈ S}`, the set
  `Y(S)` is nonempty and some `y_0 ∈ Y(S)` has `d(y_0, y) ≤ t` for all `y ∈ Y(S)`.

Property (*) holds for `X`: `d_1` is integer-valued, and a set of diameter `t` lies in a ball of radius `t`
around any of its points, whose size is bounded in terms of `t`, `k` and the degree bound.

## 2. Three lemmas

Fix a finite set `F ⊆ X`. Let `Q_i ⊆ |T_i|` be the geometric realization of the convex hull (finite subtree) of
the `i`-th coordinates of `F`, and `P = Q_1 × ⋯ × Q_k`. `P` is a compact contractible polyhedron of dimension
`≤ k`. Extend `d_1` to `P` by the same formula. Give `P` the l^2 product metric `d_2`, which is CAT(0); its
geodesics are the products of constant-speed geodesics of the factors.

**Lemma J (Jensen at the barycentre, trees).** Let `Q` be a finite metric tree, `μ` a finitely supported
probability measure on `Q`, and `b` a minimizer of `F(c) = ∫ d(c,y)^2 dμ(y)` (one exists: `F` is continuous and
`Q` compact). Then `d(x, b) ≤ ∫ d(x,y) dμ(y)` for every `x ∈ Q`.

*Proof.* Let `L = d(x,b) > 0` (the case `L = 0` is trivial), and let `p : Q → [x,b]` be the nearest-point
projection. Put `s(y) = d(x, p(y)) ∈ [0, L]`. In a tree the geodesic from `x` to `y` passes through `p(y)`, and
if `p(y) = b` the geodesic from `y` to any point of `[b,x]` passes through `b`. Let `b_ε ∈ [b,x]` with
`d(b, b_ε) = ε`, where `0 < ε < min{L − s(y) : y ∈ supp μ, p(y) ≠ b}` (or `ε < L` if that set is empty). Then
`d(b_ε, y) = d(b,y) + ε` if `p(y) = b`, and `d(b_ε, y) = d(b,y) − ε` if `p(y) ≠ b`. Hence
`0 ≤ F(b_ε) − F(b) = 2ε (∫_{p=b} d(b,y) dμ − ∫_{p≠b} d(b,y) dμ) + ε^2`. Letting `ε → 0` gives
(1) `∫_{p=b} d(b,y) dμ ≥ ∫_{p≠b} d(b,y) dμ`.
Now `d(x,y) = L + d(b,y)` if `p(y) = b`, and `d(x,y) = s(y) + d(p(y),y)` with
`d(b,y) = (L − s(y)) + d(p(y),y)` if `p(y) ≠ b`. So
`∫ d(x,y) dμ − L = ∫_{p=b} d(b,y) dμ + ∫_{p≠b} [d(b,y) − 2(L − s(y))] dμ`.
By (1) this is at least `∫_{p≠b} [2 d(b,y) − 2(L − s(y))] dμ = 2 ∫_{p≠b} d(p(y), y) dμ ≥ 0`. ∎

**Consequence (products).** For a finitely supported probability measure `μ` on `P` with marginals `μ_i`, let
`b = (b_1,…,b_k)` with `b_i` given by Lemma J for `μ_i` (so `b ∈ P`). For every `x ∈ P`,
`d_1(x,b) = Σ_i d(x_i,b_i) ≤ Σ_i ∫ d(x_i,y_i) dμ = ∫ d_1(x,y) dμ(y)`.
In particular, for points `s_0, …, s_p ∈ P` and `μ` uniform on them,
(2) `d_1(s_j, b) ≤ (1/(p+1)) Σ_l d_1(s_j, s_l)` and `d_1(z, b) ≤ (1/(p+1)) Σ_l d_1(z, s_l)` for all `z ∈ P`.

**Lemma H (Helly number k+1).** For `z ∈ P` and `ρ ≥ 0` put `B(z,ρ) = {c ∈ P : d_1(z,c) ≤ ρ}`. If `𝓑` is a
finite family of such sets and every `k+1` members of `𝓑` intersect, then all of `𝓑` intersect.

*Proof.* Each `B(z,ρ)` is closed, and it is convex for `d_2`: along a `d_2`-geodesic `c(λ) = (c_i(λ))` each
`d(z_i, c_i(λ))` is convex, because distance to a point in a tree is convex along constant-speed geodesics. So
the sum is convex. Nonempty intersections of members are compact convex subsets of a CAT(0) polyhedron. They are
contractible (geodesic contraction), locally contractible and finite-dimensional, hence ARs. Suppose `𝓑` has
empty intersection, and let `K_0, …, K_m` be a minimal subfamily with empty intersection. Every `k+1` members
intersect, so `m ≥ k+1 ≥ 2`. The nerve of `{K_j}` is `∂Δ^m ≃ S^{m−1}`. By Borsuk's nerve theorem for finite
closed covers by ARs with AR-or-empty intersections, `U = ∪ K_j ≃ S^{m−1}`, so `Ȟ^{m−1}(U) ≠ 0` with
`m − 1 ≥ k`. But for every compact `A ⊆ P` and `j ≥ k ≥ 1`, `Ȟ^j(A) = 0`. For `j > k` this holds because
`dim A ≤ k`. For `j = k` use the exact sequence `Ȟ^k(P) → Ȟ^k(A) → Ȟ^{k+1}(P,A)`: `Ȟ^k(P) = 0` since `P` is
contractible, and `Ȟ^{k+1}(P,A) ≅ Ȟ^{k+1}(P/A) = 0` since `P/A` is compact metrizable of dimension `≤ k`
(countable sum theorem applied to the σ-compact `P \ A` plus one point). Contradiction. ∎

**Lemma R (rounding).** Every `c ∈ P` has a vertex `v ∈ X` with `d_1(c,v) ≤ k/2`. Take the nearest vertex in
each coordinate. So `d_1(x,v) ≤ d_1(x,c) + k/2` for all `x`.

## 3. Verification of Theorem 3.1

Fix an integer `t ≥ k(k+1)` and put `r_t = kt/(k+1) + k/2`. Then `r_t < t` (since `t > k(k+1)/2`) and
(3) `r_t ≤ t − k/2`, which is equivalent to `t ≥ k(k+1)`.

**Balls.** Let `S ⊆ X` with `diam S = t`, and consider the family `C_s = B(s, kt/(k+1))`, `s ∈ S`, inside `P`
built from `F = S`. Any `p+1 ≤ k+1` points `s_0..s_p` have a barycentre `b` with
`d_1(s_j,b) ≤ (p/(p+1)) t ≤ kt/(k+1)` by (2). So every `k+1` members intersect, and by Lemma H there is
`c ∈ ∩ C_s`. By Lemma R there is a vertex `y` with `d_1(s,y) ≤ r_t` for all `s`. So `S` lies in a ball of radius
`r_t < t`, and `Y(S) ≠ ∅`.

**Centres.** `Y = Y(S)` is finite. Build `P` from `F = S ∪ Y` and consider the finite family `𝓑` made of
`C_s = B(s, kt/(k+1))` for `s ∈ S` and `D_y = B(y, t − k/2)` for `y ∈ Y`. Take at most `k+1` members, indexed by
`s_1..s_p` and `y_1..y_q`.
- If `p ≥ 1`, let `b` be the barycentre of the uniform measure on `s_1..s_p`. By (2),
  `d_1(s_j,b) ≤ ((p−1)/p) t ≤ kt/(k+1)`. Also `d_1(y_j,b) ≤ (1/p) Σ_l d_1(y_j, s_l) ≤ r_t ≤ t − k/2`, by (3)
  and because `y_j ∈ Y`.
- If `p = 0`, any `s ∈ S` works: `d_1(y_j, s) ≤ r_t ≤ t − k/2`.
By Lemma H there is `c ∈ ∩ 𝓑`. Round it to a vertex `y_0` (Lemma R). Then `d_1(s, y_0) ≤ kt/(k+1) + k/2 = r_t`
for all `s ∈ S`, so `y_0 ∈ Y`. And `d_1(y, y_0) ≤ t − k/2 + k/2 = t` for all `y ∈ Y`. This is the centre
hypothesis.

Both hypotheses hold for every integer `t ≥ k(k+1)`. Since `d_1` is integer-valued, `diam S` is an integer. So
for every integer `t_0 ≥ k(k+1) − 1` they hold for all `t > t_0`, and Theorem 3.1 gives `VR_{t_0}(X)`
contractible. ∎

## 4. Scope and what does not transfer

- For lines this reproves arXiv:2410.11993, Corollary 3.2 (`t ≥ n^2 + n − 1`): Lemma J plus Lemma H replace
  Bohnenblust's Jung bound and the Euclidean Helly theorem.
- General CAT(0) cube complexes. Lemma R and Lemma H should transfer, provided `d_1`-balls are contractible with
  contractible intersections. Lemma J is the obstacle. A vertex average `w_h = μ(y on the + side of h)` over
  hyperplanes is not a point of the complex, and it is unclear whether `d_1(x,·)` is convex along CAT(0)
  geodesics once the complex is not a product. The first case outside products is `Z × (Z^2 * Z)`: the triangle
  with a pendant vertex, `Γ = K_1 * (K_2 ⊔ K_1)`, of dimension 3.
- Novelty: the three sources read (Virk 2405.09134; Li–Sánchez Saldaña 2608.24279; Hulbert–Zaremsky 2608.25614)
  do not state this theorem. Li–Sánchez Saldaña treat `Z^n × F` with `F` finite and remark that the finite
  diameter of `F` is essential to their method. No wider literature search was possible from this lane (search
  budget exhausted).
