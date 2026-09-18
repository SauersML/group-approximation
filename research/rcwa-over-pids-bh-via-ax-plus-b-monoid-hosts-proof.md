---
rg: 2
id: rcwa-over-pids-bh-via-ax-plus-b-monoid-hosts-proof
kind: route
title: Li's degree-map finiteness theorem for the ax+b monoid of a PID (or its digit submonoid over F_q[t]) times a binary rose, Kunneth plus Li's vanishing theorem for perfectness, Matui for simplicity, and extension of RCWA maps to the completion
target: rcwa-groups-over-pids-satisfy-boone-higman
requires:
  - ct-p-z-is-a-one-vertex-k-graph-full-group
---

Notation is that of the target.
- **Rings and primes.** `K = Frac(R)`. Fix a generator `π_p` for each `p ∈ P`, and let `S_P`
  be the monoid of `P`-smooth elements `u ∏ π_p^{e_p}` (`u ∈ R^*`). For `e ∈ N^P` write
  `π^e = ∏ π_p^{e_p}`.
- **Affine maps.** A pair `(r, m) ∈ K × K^*` stands for the affine map `x ↦ r + m x`, so
  `(r, m)(r', m') = (r + m r', m m')` in the group `Aff(K)`.
- **The space.** `X_P = ∏_{p ∈ P} R_p = lim R/π^e R`, a Cantor set, and `R` is dense in it
  by the Chinese remainder theorem.
- **Boxes.** `B(r, m) = r + m X_P` for `m ∈ S_P`. Boxes form a basis of clopen sets, and
  `B(r, m) ∩ R = r + mR`, since `m` is `P`-smooth.

## Step 1. The monoids

- **Cases (a), (c).** `C = M_P := R ⋊ S_P = {(r, m) : r ∈ R, m ∈ S_P}`, with unit group
  `C^* = R ⋊ R^*`.
- **Case (b).** `C = D_P := {(r, m) : m ∈ S_P, deg r < deg m}`.
  - It is closed under composition, because `deg(r + m r') < deg m + deg m'`.
  - Its unit group is `C^* = {(0, u) : u ∈ F_q^*}`.
  - The full ax+b monoid is not used here, because its unit group `F_q[t] ⋊ F_q^*` is
    not finitely generated.

Let `d(r, m) = (v_p(m))_{p ∈ P} ∈ N^P`.

**Lemma 1.** For `C = M_P` or `D_P`:
1. `C` is cancellative, and `d` is a homomorphism with `d^{-1}(0) = C^*`.
2. `d` has Li's unique factorization property (UFP*).
3. `C` has lcms: `aC ∩ bC` is empty or equal to `cC`. Under `aC ↦ B_a := a(X_P)` this
   corresponds exactly to `B_a ∩ B_b = ∅` or `B_c`.
4. Up to right multiplication by units, the elements of degree `e` correspond to
   `R/π^e R`. There are finitely many, and at least `2` when `e ≠ 0`.
5. `C^*` is of type `F_∞`.

*Proof.*
1. `C` is a submonoid of the group `Aff(K)`. `(r, m)` is invertible in `C` iff `m ∈ R^*`,
   and in case (b) also `r = 0`, since `deg r < 0`.
2. Let `c = (r, m)` with `d(c) = e + f`.
   - **Existence.** Write `m = π^e m_2`.
     - In case (a) take `a = (r, π^e)` and `b = (0, m_2)`.
     - In case (b) take `a = (r_1, π^e)` with `r_1 = r mod π^e`, and
       `b = ((r − r_1)/π^e, m_2)`, which lies in `D_P` because
       `deg((r − r_1)/π^e) < deg m − deg π^e`.
   - **Uniqueness up to units.** Let `c = a'b'` with `a' = (r'_1, n)` and `d(a') = e`.
     Then `n = π^e u` with `u ∈ R^*`, and `r − r'_1 ∈ nR`.
     - In case (a), `a^{-1}a' = (π^{-e}(r'_1 − r), u)`, which lies in `C^*`.
     - In case (b), `r'_1 = r_1` (the reduced residue), so `a' = a(0, u)`.
     - In both cases `b' = u^{-1} b` by cancellation.
3. **The right ideal of `(r, m)`.**
   - In case (a), `(r, m)C` is the set of `(s, n)` with `n ∈ m S_P` and `s ∈ r + mR`.
   - In case (b) it is the same, with `deg s < deg n`. Here `(s − r)/m` automatically
     has degree `< deg(n/m)`.
   - So `aC ⊆ bC` iff `B_a ⊆ B_b`.
   - **Intersections.** By the Chinese remainder theorem in the PID `R`,
     `(r + mR) ∩ (r' + m'R)` is empty or `r'' + lR` with `l = lcm(m, m') ∈ S_P`.
   - Hence `(r, m)C ∩ (r', m')C = (r'', l)C` or `∅`. In case (b) reduce `r''` mod `l`.
4. `(r, m)(v, u) = (r + mv, mu)`, with `v = 0` in case (b). So the classes of degree `e`
   are the pairs (residue class of `r` mod `π^e`, ideal `π^e R`). There are `|R/π^e R|` of
   them.
5. **Case (a).** `O_K ≅ Z^n`, and `O_K^* ≅ μ_K × Z^s` (Dirichlet). So `O_K ⋊ O_K^*` is
   polycyclic-by-finite. It has a torsion-free polycyclic subgroup of finite index, which
   has a finite `K(π,1)`. So it is `F_∞`.
   - **Case (b).** `C^*` is finite.
   - **Case (c)** is Step 8. ∎

**Adding the binary rose.** Let `C' = C × F_2^+`, with degree `d' = (d, length) ∈ N^P × N`.
Lemma 1 (1)–(5) holds for `C'` componentwise:
- `F_2^+` is cancellative with trivial units;
- its words factor uniquely by length;
- `wF_2^+ ∩ w'F_2^+` is the longer word's ideal, or empty;
- it has `2^j` words of length `j`.

Also `C'^* = C^*`.

## Step 2. `F_∞`

Apply Li, arXiv:2110.04505v2, Theorem `thm:deg` and the lemma after it, which together
make Corollary `intro:deg`. Take Li's degree monoid to be `N^{|P|+1}`, with the Garside family of
nonzero `0/1`-vectors, as in Li's §`ss:k-graphs`, where the same pair is used for Theorem
`thm:k-graphs`.
- `C'` has one object, is left cancellative, and has a degree map with (UFP*), by
  Lemma 1 (1)–(2).
- Each `v \dot d^{-1}(p)` is finite, by Lemma 1 (4).
- Condition (F) holds because `C'` is right cancellative (Li l.1456).
- Condition (t < d) holds by Li's lemma after `thm:deg`: the degree monoid is commutative,
  hence left reversible, and every degree in the Garside family has at least `2` elements.
- `C'^*(v, v) = C^*` is `F_∞`, by Lemma 1 (5).

Hence `F(I_l(C') ⋉ ∂Ω)` is of type `F_∞`.

## Step 3. The groupoid concretely

The following identification is standard (the same as the k-graph case in
`ct-p-z-is-a-one-vertex-k-graph-full-group`) and was not re-read at source.
- **The boundary.**
  - By Lemma 1 (3), the nonempty constructible right ideals `aC'` form a semilattice
    isomorphic to the semilattice of rectangles `B_a × C(w)`, with `∅` corresponding to
    `∅`.
  - Each rectangle is the finite disjoint union of its sub-rectangles of any larger
    degree, by Lemma 1 (4).
  - So the boundary characters are exactly those given by points. This gives
    `∂Ω = X_P × C`, and `λ_a` acts as `a` from `X_P × C` onto the rectangle of `a`.
- **Germs.**
  - `C'` embeds in the group `Aff(K) × F(0,1)`. So every element of `I_l(C')` is the
    restriction of left multiplication by some group element `γ`.
  - Two distinct `γ` disagree on every nonempty open set, because affine maps and
    prefix replacements are determined on any open set.
  - Hence Exel's germs are the geometric germs, and `I_l(C') ⋉ ∂Ω` is the groupoid `G'`
    of germs of the maps `a b^{-1}` (`a, b ∈ C'`).
- **Product.** By Li's product identification (proof of `cor:ProdGraphs`),
  `G' ≅ G_P × G_{O_2}`. Here `G_P` is the germ groupoid of the affine maps
  `(s, n)(r, m)^{-1} : B(r, m) → B(s, n)`, and `G_{O_2}` is the groupoid of the binary rose.

`H_P(R) := F(G')`. Its elements are the homeomorphisms of `X_P × C` that are, on the pieces
of a finite partition into rectangles, of the form `(x, wy) ↦ (α(x), w'y)`, with `α` a
composite of basic affine bisections.

## Step 4. Hausdorff, essentially principal, minimal, purely infinite

- **Fixed points.** A nonidentity affine map `x ↦ αx + β` fixes at most one point of each
  domain `R_p`: the solution of `(α − 1)x = −β` if `α ≠ 1`, and none if `α = 1`, `β ≠ 0`. A
  prefix replacement `wy ↦ w'y` with `w ≠ w'` fixes at most one point.
- **Hausdorff.** So the fixed set of a basic bisection of `G'` is its whole domain (a unit
  bisection) or has empty interior. The unit-germ sets are therefore clopen, and `G'` is
  Hausdorff.
- **Essentially principal.** Points with nontrivial isotropy lie in countably many closed
  nowhere dense fixed sets. By Baire, trivial isotropy is dense. The unit space is a
  Cantor set, and `G'` is effective by Step 3.
- **Minimal.** `(s, n)(r, m)^{-1}` maps any box onto any other, and prefix replacements
  map any cylinder onto any other.
- **Purely infinite** (Matui, Definition `pi`). For a clopen set `A = ⊔ B_j × C(w_j)`, use
  `U = ⊔ {(x, w_j y) ↦ (x, w_j 0 y)}` and `V = ⊔ {(x, w_j y) ↦ (x, w_j 1 y)}`.
- **Comparison.** In the form Li uses (arXiv:2209.08087, l.804), purely infinite minimal
  holds: any finite union of rectangles maps by one compact open bisection into any
  nonempty rectangle, after splitting that rectangle into enough sub-rectangles. So `G'`
  has comparison.

## Step 5. Perfect, acyclic, simple

- **The binary rose is acyclic.** By FKPS arXiv:1808.07807, Theorem `thm:H computation`
  with `k = 1`, `|Λ^{e_1}| = 2` and `N_1 = 1`, the groupoid homology `H_*(G_{O_2})` is `0`.
- **The product is acyclic.** Matui's Künneth theorem (Adv. Math. 2016, Theorem 2.4), for
  ample Hausdorff groupoids, is quoted in FKPS l.2249–2275 as a split exact sequence
  `0 → ⊕_{i+j=n} H_i(G) ⊗ H_j(H) → H_n(G × H) → ⊕_{i+j=n−1} Tor(H_i(G), H_j(H)) → 0`.
  With `H = G_{O_2}` both ends vanish, so `H_*(G') = 0`.
- **The full group is perfect.** Li, arXiv:2209.08087, Corollary `introcor:Vanish`, applies:
  `G'` is ample and minimal, has comparison, and its unit space has no isolated points.
  It gives that `F(G')` is integrally acyclic and `F(G') = D(F(G'))`.
- **Simple.** By Matui's Theorem `simple2`, which applies by Step 4, `D(F(G'))` is simple.
  So `H_P(R)` is simple.

## Step 6. The embedding

Let `g ∈ RCWA_P(R)` have modulus `m ∈ S_P` and class representatives `r_i`, reduced
(`deg r_i < deg m`) in case (b).
- **The pieces.** `g(r_i + mz) = s'_i + n_i z` for `z ∈ R`, where `s'_i = g(r_i)` and
  `n_i = a_i m/c_i`. Here `n_i = g(r_i + m) − g(r_i) ∈ R`, and it is `P`-smooth. The classes
  `s'_i + n_i R` partition `R`.
- **The extension.** Define `ĝ(r_i + mξ) = s'_i + n_i ξ` for `ξ ∈ X_P`.
  - In cases (a) and (c), `ĝ|_{B(r_i, m)} = (s'_i, n_i)(r_i, m)^{-1}`, a basic bisection.
  - In case (b), write `s'_i = s_i + n_i v_i` with `deg s_i < deg n_i`. Then
    `ĝ|_{B(r_i,m)} = (s_i, n_i) ∘ τ_{v_i} ∘ (r_i, m)^{-1}`, where `τ_v(ξ) = ξ + v`.
  - Choose `M ∈ S_P` monic with `deg M > deg v`. Then
    `τ_v = ⊔_{deg ρ < deg M} (ρ + v, M)(ρ, M)^{-1}`, since `deg(ρ + v) < deg M`. So
    translations of `X_P` are finite unions of basic bisections: over `F_q[t]` there are no
    carries.
- **A homeomorphism.** The image boxes `B(s'_i, n_i)` are pairwise disjoint: a nonempty
  intersection of boxes is a box (Lemma 1 (3)), and it would meet `R`. Their union is
  clopen and contains the dense set `R`. So `ĝ` is a homeomorphism in `F(G_P)` extending
  `g`.
- **The embedding.** `g ↦ ĝ` is an injective homomorphism by density of `R`. So
  `ι(g) = ĝ × id_C` embeds `RCWA_P(R)` in `H_P(R)`.

## Step 7. Conclusion for (a) and (b)

A finitely generated `H ≤ RCWA(R)` has finitely many moduli and image moduli. Let `P` be
the primes dividing them, enlarged to be nonempty. Then `H ≤ RCWA_P(R)`, which embeds in
`H_P(R)`. That group is finitely presented (Step 2) and simple (Step 5).

## Step 8. Semilocalizations (c)

Let `H = ⟨g_1, …, g_k⟩ ≤ RCWA(Z_(π))`. Every modulus of `Z_(π)` is a unit times a
`π`-number.

**Reduction to `A = Z[1/N]`.** Let `N` be the product of the primes outside `π` that
divide a numerator or a denominator of a coefficient `a, b, c` of some `g_j^{±1}`. Put
`A = Z[1/N] ⊆ Z_(π)`.
- **`A` is preserved.** For `x ∈ A`, `g_j(x) = (ax + b)/c` lies in `Z[1/(N M)]` for a
  `π`-number `M`, and it lies in `Z_(π)`. Hence `g_j(x) ∈ A`. The same holds for `g_j^{-1}`,
  so `g_j|_A` is a permutation of `A`.
- **It is RCWA on `A`.** `(r + mZ_(π)) ∩ A = r + mA` for `r ∈ A`, and every image modulus
  lies in `S_π(A) = A^* · (π-numbers)`.
- **Faithfulness.** Every class of `Z_(π)` meets `A` in an infinite set, and a nonidentity
  affine map fixes at most one point. So `H` acts faithfully, and `H ≤ RCWA_π(A)`.

**The host.** `A` is a PID with `A/mA ≅ Z/m` for every `π`-number `m`. Steps 1–7 apply to
`C = A ⋊ S_π(A)` on `X_π = ∏_{p ∈ π} Z_p`, once we check Lemma 1 (5) for
`C^* = A ⋊ A^*`, where `A^* = {±1} × ⟨q_1, …, q_s⟩` for the primes `q_i | N`.
- `Z[1/(q_1⋯q_j)] ⋊ ⟨q_1, …, q_j⟩` is the ascending HNN extension of
  `Z[1/(q_1⋯q_{j−1})] ⋊ ⟨q_1, …, q_{j−1}⟩` by the injective endomorphism `x ↦ q_j x`, the
  identity on the `q_i`-part.
- Starting from `Z`, `s` such steps give `A ⋊ ⟨q_1, …, q_s⟩`. Ascending HNN extensions of
  `F_∞` groups are `F_∞`, and adjoining `−1` is a finite extension.
- So `C^*` is `F_∞`, and `H` embeds in the `F_∞` simple group `H_π(A)`. ∎

## Calibrations

- **A Collatz-type permutation.** `α(n) = 3n/2` on `0(2)`, `(3n+1)/4` on `1(4)`, `(3n−1)/4` on
  `3(4)`, in `RCWA(Z)`.
  - Its images are `0(3)`, `1(3)` and `2(3)`, since `4k+3 ↦ 3k+2`.
  - With `P = {2, 3}`, `α̂` maps `B(0,2)`, `B(1,4)`, `B(3,4)` onto `B(0,3)`, `B(1,3)`,
    `B(2,3)` in `Z_2 × Z_3`. So `⟨α, CT_{\{3\}}(Z)⟩ ≤ H_{\{2,3\}}(Z)`.
- **Gaussian integers.** `Z[i]` with `P = {(1+i)}`: the host contains the rotation
  `x ↦ ix` (a unit of `C`), all translations, and multiplication by `1+i`.
- **`F_2[t]`, `P = {t}`.** Here `X_P = F_2[[t]]`. The class shift `n ↦ n + m` on `r + mR`
  has order `2` (characteristic `2`), and its extension is a finite union of box maps.
