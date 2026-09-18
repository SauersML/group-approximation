---
rg: 2
id: higman-tree-lattice-factorization-proof
kind: route
title: Orders around the cycle force m | n^m - 1; metacyclic vertex groups glue by normal forms into K1 *_A K2, and complete bipartite links give a product of trees
target: higman-torsion-generator-quotients-factor-through-tree-lattices
requires:
  - higman-power-pair-collapse-is-base-uniform-up-to-torsion
artifacts:
  - experiments/higman-automaton-models-2026-09-18/gamma_vt.g
  - experiments/higman-automaton-models-2026-09-18/gamma_vt-output.txt
  - experiments/higman-automaton-models-2026-09-18/comm_ac.g
  - experiments/higman-automaton-models-2026-09-18/comm_ac-output.txt
  - experiments/higman-automaton-models-2026-09-18/search_sym.py
  - experiments/higman-automaton-models-2026-09-18/search_sym-output.txt
  - experiments/higman-automaton-models-2026-09-18/ss_core.py
  - experiments/higman-automaton-models-2026-09-18/gamma_e.g
  - experiments/higman-automaton-models-2026-09-18/gamma_e-output.txt
  - experiments/higman-automaton-models-2026-09-18/kk_coords.g
  - experiments/higman-automaton-models-2026-09-18/kk_coords-output.txt
---

Conventions: `x^y = y^-1 x y`, so `y^-k x y^k = x^(y^k)`. `H4(n)`, n-admissible, `Gamma(n,m)`, `G(x,y)`,
`K1`, `K2`, `L1`, `L2`, `A` and `B` are as in the target. **[U]** is
`higman-power-pair-collapse-is-base-uniform-up-to-torsion`. Only section 7 uses it, through its item 2.
Throughout, "consecutive pair" means `(x,y)` in `(a,b), (b,c), (c,d), (d,a)`. The relation of `H4(n)`
for the pair is `x^-1 y x = y^n`.

## 1. The vertex groups

**Lemma 1.1.** Let `m` be n-admissible. Then `gcd(n,m) = 1`, and
`G(x,y) = < x, y | x^m, y^m, x^-1 y x = y^n >` is the semidirect product `Z/m ⋊ Z/m`, where the
generator `x` of the acting factor acts on `Z/m = <y>` by multiplication by `n`. So `|G(x,y)| = m^2`,
`<y>` is normal, `x` and `y` both have order `m`, and `<x> ∩ <y> = 1`. Moreover `G(x,y) = <x><y>`
with unique factorization.

*Proof.*
- Since `n^m ≡ 1 (mod m)`, `n` is a unit mod `m`. So `μ : k -> nk` is an automorphism of `Z/m` with
  `μ^m = id`.
- Hence the semidirect product `S = Z/m ⋊_μ Z/m` exists. Its elements `x = (0,1)` and `y = (1,0)`
  satisfy the three relations, so `G(x,y)` maps onto `S`.
- Conversely, the relation gives `y x = x y^n`, so every word can be rewritten as `x^i y^j` with
  `0 <= i, j < m`. Hence `|G(x,y)| <= m^2 = |S|`, and the map is an isomorphism.
- The remaining assertions hold in `S`. ∎

## 2. Universality (item 1)

Let `Q` be a quotient of `H4(n)` in which the images of `a, b, c, d` have finite orders
`r_a, r_b, r_c, r_d`. Put `m = lcm(r_a, r_b, r_c, r_d)`. Take the consecutive pair `(a, b)`; the other
three are the same after applying the cyclic symmetry.

- Conjugation by `a` is an automorphism of `Q` and sends `b` to `b^n`. So `b^n` has order `r_b`, and
  `gcd(n, r_b) = 1`.
- By induction, `a^-k b a^k = b^(n^k)`. With `k = r_a` this gives `b = b^(n^(r_a))`, so
  `r_b | n^(r_a) - 1`.
- Since `r_a | m`, `n^(r_a) - 1` divides `n^m - 1`. Hence `r_b | n^m - 1`.

Doing this for all four pairs gives `r_x | n^m - 1` for every `x`, so `m = lcm(r_x)` divides `n^m - 1`
and `m` is n-admissible. Finally `x^m = 1` in `Q` for every generator `x`, so `Q` is a quotient of
`Gamma(n,m)`. ∎

## 3. Arithmetic (item 2)

- **Admissible implies coprime to `n`.** If `m | n^m - 1`, then `n · n^(m-1) ≡ 1 (mod m)`.
- **Smallest prime.** Let `m > 1` be admissible, and let `p` be its smallest prime factor.
  - `n^m ≡ 1 (mod p)`, and `p` does not divide `n`. So `t = ord_p(n)` divides both `m` and `p - 1`.
  - Every prime factor of `t` divides `m`, so it is at least `p`. It also divides `p - 1`, so it is
    below `p`. Hence `t` has no prime factors: `t = 1`, and `p | n - 1`.
- **Prime powers.** Let `p | n - 1`.
  - If `x ≡ 1 (mod p^j)` with `j >= 1`, then `x^p ≡ 1 (mod p^(j+1))`. This is the binomial theorem:
    `x^p - 1 = (x-1)(x^(p-1) + ... + 1)`, and the second factor is `≡ p ≡ 0 (mod p)`.
  - So `n^(p^(k-1)) ≡ 1 (mod p^k)`, hence `n^(p^k) ≡ 1 (mod p^k)`.
- **lcm.** If `m_1` and `m_2` are admissible and `L = lcm(m_1, m_2)`, then `ord_(m_i)(n)` divides
  `m_i`, which divides `L`. So `n^L ≡ 1 (mod m_i)` for both `i`, hence `n^L ≡ 1 (mod L)`.
- **Example `m = 20`, `n = 3`.** `3^2 ≡ 1 (mod 8)` gives `4 | 3^20 - 1`, and `3^4 ≡ 1 (mod 5)` gives
  `5 | 3^20 - 1`.
- **`n = 2`.** `n - 1 = 1` has no prime factor, so no `m > 1` is admissible. So if all four generators
  of a quotient of `H4` are torsion, then `m = 1` by section 2, and the quotient is trivial. ∎

## 4. The amalgam structure (item 3)

Fix an n-admissible `m`. Define three abstract groups:
- `K1^ = G(a,b) *_<b> G(b,c)`, identifying the two copies of `<b>`, which are cyclic of order `m` by
  Lemma 1.1;
- `K2^ = G(c,d) *_<d> G(d,a)`;
- `A^ = <α> * <γ> ≅ Z/m * Z/m`.

We use the normal form theorem for amalgams (Serre, *Trees*, I.1.2, Thm 1; Lyndon–Schupp IV.2.6).
Suppose `g_1 ... g_k` has `k >= 1` factors, taken alternately from the two vertex groups, and no factor
lies in the amalgamated subgroup. Then `g_1 ... g_k` is not in the amalgamated subgroup; in
particular it is not `1`.

**Lemma 4.1.** The maps `A^ -> K1^` (`α -> a`, `γ -> c`) and `A^ -> K2^` (`α -> a`, `γ -> c`) are
injective. Their images meet the amalgamated subgroups trivially: `A ∩ <b> = 1` in `K1^`, and
`A ∩ <d> = 1` in `K2^`.

*Proof.*
- A nontrivial element of `A^` is a reduced alternating word `α^(i_1) γ^(j_1) ...` with all exponents
  nonzero mod `m`.
- In `K1^` its image is a product whose factors alternate between `a^i` in `G(a,b)` and `c^j` in
  `G(b,c)`.
- By Lemma 1.1, applied to `(x,y) = (a,b)` and to `(x,y) = (b,c)`, none of these factors lies in `<b>`.
  So the normal form theorem gives both claims for `K1^`.
- For `K2^`, the factor `c^j` lies in `G(c,d) \ <d>`, by Lemma 1.1 with `(x,y) = (c,d)`, and `a^i` lies
  in `G(d,a) \ <d>`, with `(x,y) = (d,a)`. ∎

**Lemma 4.2.** `Gamma(n,m) ≅ K1^ *_A^ K2^`. Hence:
- `K1^`, `K2^`, `A^` and all four `G(x,y)` embed in `Gamma(n,m)`, with images `K1`, `K2`, `A` and
  `<x,y>`;
- `A ≅ Z/m * Z/m`;
- every generator has order exactly `m`.

*Proof.*
- By Lemma 4.1 the pushout of `K1^ <- A^ -> K2^` is an amalgamated free product.
- A presentation of the pushout has generators `a, b, c` (for `K1^`) and `c', d, a'` (for `K2^`). The
  relations are those of `G(a,b)`, `G(b,c)`, `G(c',d)` and `G(d,a')`, together with `a' = a` and
  `c' = c`.
- Eliminating `a'` and `c'` leaves generators `a, b, c, d`, with relations `x^m` for all four
  generators and the four relations `x^-1 y x = y^n`. This is the defining presentation of
  `Gamma(n,m)`.
- Factors of an amalgam embed, so `K1^`, `K2^` and `A^` embed.
- `G(x,y)` embeds in `K1^` or `K2^`, as a factor. So `x` has order `m` by Lemma 1.1. ∎

**Lemma 4.3 (index and coset action).**
- `K1 = <b> · A`, and `b^j A = b^k A` only if `j ≡ k (mod m)`. So `[K1 : A] = m`, with transversal
  `<b>`.
- On `K1/A` the generators act as `b : j -> j+1`, `a : j -> n^-1 j` and `c : j -> j`. Here `n^-1` is
  the inverse of `n` mod `m`.
- More precisely, `a b^j = b^(n^-1 j) a` and `c b^j = b^j c^(n^j)`.
- The same holds for `K2`, with `(a, b, c)` replaced by `(c, d, a)`.

*Proof.*
- **Distinct cosets.** If `b^j A = b^k A`, then `b^(k-j)` lies in `A ∩ <b> = 1` (Lemma 4.1), and `b` has
  order `m`.
- **Commutation rule for `a`.** From `a^-1 b^k a = b^(kn)` we get `b^k a = a b^(kn)`. Put `j = kn`;
  since `n` is a unit mod `m`, this gives `a b^j = b^(n^-1 j) a`.
- **Commutation rule for `c`.** From `b^-1 c b = c^n`, induction gives `b^-j c b^j = c^(n^j)`, so
  `c b^j = b^j c^(n^j)`. The exponent `n^j` is well defined mod `m` for `j` in `Z/m`, because
  `n^m ≡ 1 (mod m)`.
- **The cosets cover `K1`.** The finite set `{b^j A}` is mapped into itself by left multiplication by
  `a`, `b` and `c`, and these maps are injective, so they are permutations of it. Since `a, b, c`
  generate `K1`, the set is a single `K1`-orbit containing `A`. So it is `K1/A`.
- **`K2`.** Use the relations `c^-1 d c = d^n` and `d^-1 a d = a^n`. ∎

**Symmetry and finite subgroups.**
- The rotation `σ : a -> b -> c -> d -> a` preserves the presentation of `Gamma(n,m)`. It carries
  `K1 -> L2`, `K2 -> L1` and `A -> B`. Hence `Gamma(n,m) = L2 *_B L1`, with `B ≅ Z/m * Z/m` of index
  `m` in both factors.
- A finite group acting on a tree fixes a vertex (Serre, *Trees*, I.4.3). So a finite subgroup of an
  amalgam is conjugate into a factor.
- Apply this to `K1 *_A K2`, and then to `K1 = G(a,b) *_<b> G(b,c)` and to
  `K2 = G(c,d) *_<d> G(d,a)`. So every finite subgroup of `Gamma(n,m)` is conjugate into some `G(x,y)`.
  This completes item 3. ∎

## 5. Geometry (item 4)

**The square of groups.**
- Take a Euclidean unit square with vertices `v_ab, v_bc, v_cd, v_da` and edges
  `e_b = [v_ab, v_bc]`, `e_c = [v_bc, v_cd]`, `e_d = [v_cd, v_da]`, `e_a = [v_da, v_ab]`.
- The vertex `v_xy` gets the group `G(x,y)`, the edge `e_x` gets `<x>`, and the face gets `1`.
- The inclusions are the obvious ones: `<x>` lies in the groups of both endpoints of `e_x`.
- The fundamental group is the colimit. Its presentation is the one in Lemma 4.2, so it is
  `Gamma(n,m)`.

**Non-positive curvature.**
- The local development at `v_xy` has as its link the bipartite graph `Λ_xy`. Its vertex set is
  `G/<x> ⊔ G/<y>`, with `G = G(x,y)`. Each `g in G` is an edge joining `g<x>` and `g<y>`.
- The edges have angle `π/2`, so the link condition means girth at least 4.
- A bipartite graph has girth at least 4 exactly when it has no double edges.
- Two elements `g` and `g'` join the same pair exactly when `g^-1 g'` lies in `<x> ∩ <y> = 1`
  (Lemma 1.1).
- So the square of groups is non-positively curved. By the Gersten–Stallings theorem
  (Bridson–Haefliger, *Metric spaces of non-positive curvature*, II.12.28 and II.12.29), it is
  developable, and its development `X` is a CAT(0) square complex.
- `Gamma(n,m)` acts on `X` with quotient the square and with the local groups as stabilizers. So it
  acts properly and cocompactly, and freely transitively on squares, since the face group is trivial.

**Complete bipartite links.**
- The edges of `Λ_xy` joining `g<x>` and `h<y>` are the elements of `g<x> ∩ h<y>`.
- `G = <y><x>`: this is Lemma 1.1 after passing to inverses. So `h^-1 g <x>` meets `<y>`, which means
  the intersection is nonempty.
- It has at most one element, because `<x> ∩ <y> = 1`.
- So every link of `X` is `K_(m,m)`.

**Product of trees.**
- A CAT(0) square complex whose vertex links are all complete bipartite is a product of two trees.
  See Burger–Mozes, *Lattices in product of trees*, Publ. IHES 92 (2000), §1, and Wise, *Complete
  square complexes*, Comment. Math. Helv. 82 (2007).
- The partition of the edges into the two directions is the partition into the types `{a, c}` and
  `{b, d}`. Opposite edges of the square are parallel. `Gamma(n,m)` preserves edge types, so it
  preserves the factors.
- Both factor trees are `m`-regular, because each side of `K_(m,m)` has `m` vertices.
- Consider the factor `T_B` in which the `e_b` and `e_d` edges project to edges.
  - The stabilizer of a vertex `u` of `T_B` acts on the fibre `{u} x T_A`. That fibre is a tree of
    `e_a`-edges with quotient `e_a`, so the stabilizer is `G(d,a) *_<a> G(a,b) = L1`.
  - The stabilizer of an edge `ε` of `T_B` acts on the midline tree of the slab `ε x T_A`. Its
    quotient is a single edge joining the midpoints of `e_b` and `e_d`, with trivial edge group, so
    the stabilizer is `<b> * <d> = B`.
  - So `T_B` is the Bass–Serre tree of `L1 *_B L2`. By the symmetry `σ`, `T_A` is that of
    `K1 *_A K2`.

**Special cases.**
- If `m | n - 1`, then `y^x = y^n = y`, and each `G(x,y) = Z/m x Z/m`.
  - `Gamma(n,m)` is then the graph product of four copies of `Z/m` over the 4-cycle `a-b-c-d-a`. That
    is `(<a> * <c>) x (<b> * <d>) = A x B`.
  - For `m = 2` and odd `n`, `a, c` act as the reflections `x -> -x` and `x -> 1-x`, and `b, d` act as
    `y -> -y` and `y -> 1-y`. This is the group `D_oo x D_oo` of [U], item 4.
- If `m` does not divide `n - 1`, then `a^-1 b a = b^n != b`, and the local action of `G(a,b)` on the
  `m` directions `G/<a>` is not regular. For example, `G(a,b)` acts on `G/<a>` with kernel
  `<a^(ord_m n)>`. ∎

## 6. Relators inside the edge group (the reduction)

**Lemma 6.1.** Let `R` be an element of `A`. Put `N_A = <<R>>_A`, `N_i = <<R>>_(K_i)` and
`Abar = A/N_A`. Suppose that `N_i ∩ A = N_A` for `i = 1, 2`, which means `Abar` embeds in `K_i/N_i`.
Then
`Gamma(n,m)/<<R>> ≅ (K1/N1) *_Abar (K2/N2)`.
In particular `K_i/N_i` and `Abar` embed, and `a` has the same order in `Gamma(n,m)/<<R>>` as in
`Abar`.

*Proof.*
- `Gamma(n,m) = K1 *_A K2` is presented by the presentations of `K1` and `K2`, together with the
  identification of the two copies of `A`.
- Add `R` to this presentation. Since `R` is identified with its copy in `K2`, the result presents the
  pushout of `K1/N1 <- A -> K2/N2`.
- Both maps factor through `Abar`, and by hypothesis both induced maps from `Abar` are injective. So the
  pushout is the amalgam, and factors of an amalgam embed. ∎

**Corollary 6.2.** Take `n = 3` and `R = [a,c]^2`. Suppose the hypothesis of Lemma 6.1 holds for
infinitely many `m = 2^e`. Then `a` has infinite order in `H4(3)/<<[a,c]^2>>`.

*Proof.*
- `Abar_m = <a, c | a^m, c^m, [a,c]^2>` maps onto `Z/m x Z/m`, so `a` has order `m` in `Abar_m`.
- By Lemma 6.1, `a` then has order `m` in `Gamma(3,m)/<<R>>`, which is a quotient of
  `H4(3)/<<R>>`.
- This holds for infinitely many `m`. ∎

**The induced representation.**
- Lemma 4.3 gives the Kaloujnine–Krasner embedding `K1 -> A wr Sym(m)`, taken with respect to the
  transversal `t_j = b^j`. It is defined by `g t_j = t_(g·j) φ_j(g)`.
- By Lemma 4.3, `φ_j(a) = a`, `φ_j(b) = 1` and `φ_j(c) = c^(n^j)`.
- Follow `t_j` through the letters of `[a,c] = a^-1 c^-1 a c`:
  - `c t_j = t_j c^(n^j)`;
  - `a t_j = t_(n^-1 j) a`;
  - `c^-1 t_(n^-1 j) = t_(n^-1 j) c^(-u)`;
  - `a^-1 t_(n^-1 j) = t_j a^-1`.
- Hence `φ_j([a,c]) = a^-1 c^-u a c^v`, where `u = n^(n^-1 j)` and `v = n^j`.
- Compose with `A -> Abar` in each coordinate. The resulting map `K1 -> Abar wr Sym(m)` kills `R` iff
  two conditions hold: `R` fixes every coset, and every `φ_j(R)` lies in `N_A`.
- If it kills `R`, then `N_1 ∩ A ⊆ N_A`, because `φ_0` restricted to `A` is the quotient map. That is
  the hypothesis of Lemma 6.1 for `K1`.

**Proposition 6.3 (the case `m | n + 1`).** Let `m` be even with `m | n + 1`; such an `m` is
admissible, since `n ≡ -1` and `m` is even. Let `R` be a word in `A` whose exponent sums in `a` and in
`c` are both even. Suppose `<<R>>_A` contains `R(a, c^-1)` and `R(a^-1, c)`. Then
`Gamma(n,m)/<<R>> = (K1/N1) *_Abar (K2/N2)`.

For `R = [a,c]^2` the hypothesis holds, because `[a, c^-1]^2 = c [a,c]^-2 c^-1` and
`[a^-1, c]^2 = a [a,c]^-2 a^-1`. So for instance
`Gamma(3,4)/<<[a,c]^2>> = (K1/N1) *_(<a,c | a^4, c^4, [a,c]^2>) (K2/N2)`.

*Proof.*
- Since `n ≡ n^-1 ≡ -1 (mod m)` and `m` is even, `a` acts on `K1/A` by `j -> -j`, which preserves the
  parity of `j`. Also `φ_j(c) = c^((-1)^j)`.
- So `φ_j(w) = w(a, c^((-1)^j))` for every word `w` fixing all cosets. The permutation of `R` is
  `j -> (-1)^(e_a(R)) j`, which is trivial.
- For `K2` the roles of `a` and `c` are exchanged: `a` acts trivially on `K2/A`, `c` acts by
  `j -> -j`, and `φ_j(a) = a^((-1)^j)`.
- Apply the criterion above, and then Lemma 6.1. ∎

**Where the induced representation fails.** For `n = 3` and `m = 8` the coordinates for odd `j` are
`[a, c^3]`. `kk_coords-output.txt` shows that `[a, c^3]^2` has nontrivial image in a finite 2-quotient
of `Abar_8`, so it is not in `N_A`. The same happens for `m = 16`, where odd `j` gives `(u,v) = (11,3)`
or `(3,11)`. So for `m >= 8` the hypothesis of Lemma 6.1 needs a genuine Freiheitssatz for the proper
power `[a,c]^2` over the virtually free group `K1`, beyond the induced representation.

## 7. Edge images in the torsion regime (item 5)

- **The quotient killing `b` and `d`.** Setting `b = d = 1` turns the relations into `1 = 1`,
  `c = c^n`, `1 = 1` and `a = a^n`. So `H4(n)/<<b,d>> = <a, c | a^(n-1), c^(n-1)> = Z/(n-1) * Z/(n-1)`.
- Hence every group `P` generated by two elements whose orders divide `n - 1` is a quotient with
  `A = P` and `B = 1`.
- The Gupta–Sidki 3-group is generated by two elements of order 3, which gives the `n = 4` example.
- **Edge images in `X`.** Let the edge image `A` lie in `X`. Then [U], item 2, makes all four
  generators torsion, so section 2 applies, and `A` is the image of `Z/m * Z/m` (Lemma 4.2). ∎

## 8. The computations (item 6)

All runs used GAP's `EpimorphismPGroup(G, 2, k)`, the largest class-`k` quotient in the lower
exponent-2 central series. This is a finite computation with certified output.

- **`gamma_vt.g`.**
  - In the class-`e` quotient `P_e` of `Gamma(3,2^e)`, for `e = 2..5`, each of `<a,b>`, `<b,c>`,
    `<c,d>`, `<d,a>` has order `2^(2e)`.
  - By Lemma 1.1 these are the vertex groups, which therefore inject.
  - By section 4, every finite subgroup is conjugate into a vertex group. So `ker(Gamma(3,2^e) -> P_e)`
    is torsion-free, of index `|P_e| = 2^10, 2^20, 2^36, 2^64`.
  - The second half of the script adds `[a,c]^2`.
- **`gamma_e.g`.** This is the same family without the vertex-group check, for classes `e..e+2`. The
  generators keep order exactly `2^e`, as they must by Lemma 4.2.
- **`comm_ac.g`.** This is the `[a,c]` calibration.
- **`kk_coords.g`.** These are the coordinates of section 6.
- **`search_sym.py`, with `ss_core.py`.**
  - This is an exhaustive enumeration of the 8450 cyclically symmetric recursions with sections of
    length at most 2, checked to level 10.
  - The data are consistent with item 1, but nothing in the proof depends on this search.
