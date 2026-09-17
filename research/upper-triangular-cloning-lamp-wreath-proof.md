---
rg: 2
id: upper-triangular-cloning-lamp-wreath-proof
kind: route
title: "Root-split unipotent blocks of T(B_*(R)) form R[D] ⊗ LC, normalized by F_L × F_R, giving (R,+) ≀ Z^2"
target: upper-triangular-cloning-groups-contain-lamp-wreath-z2
requires: []
artifacts:
  - experiments/zaremsky-2-16-upper-triangular-2026-09-17/lamplighter_in_upper_triangular_cloning.py
  - experiments/zaremsky-2-16-upper-triangular-2026-09-17/output.txt
---

Direct proof. The only imports are the definition of `T(G_*)` and the Witzel–Zaremsky cloning maps on
`B_n(R)`, quoted below. Numerical cross-checks over `F_3` are in
`experiments/zaremsky-2-16-upper-triangular-2026-09-17/`. They cover:
- the cloning axioms for `n ≤ 5`;
- block shape and invariance of `Φ` under 360 random expansions;
- the relations of `F_3 ≀ Z^2` and a free product orbit on the window `|i|, |j| ≤ 3`, computed
  with an implementation of the group product.

## 0. Imports (verbatim)

**Witzel–Zaremsky, arXiv:1405.5491, §7** (PDF text extracted 2026-09-17).
- The cloning map is displayed in block form as

  `κk = [[A<,<, A<,k, A<,k, A<,>], [Ak,<, Ak,k, 0, 0], [0, 0, Ak,k, Ak,>], [A>,<, A>,k, A>,k, A>,>]]`

  "where the matrix has a block structure under which the middle column and row are the kth column
  and row of the full matrix respectively." (The display is transcribed row by row.)
- "We therefore restrict to the groups Bn(R) of invertible upper triangular matrices."
- "Lemma 7.1. The trivial morphisms ρn and the maps κn_k defined above describe a properly graded
  cloning system on B∗(R)."
- "for any A ∈ Mn(R), ((A)κk)i,j = Aπk(i),πk(j) unless i = k or i > j (here πk is as in Example 2.9)".
  Example 2.9, (2.3): "πk(m) = m for m ≤ k, m − 1 for m > k".
- "Elements are represented by triples (T−,A,T+) for trees T± with n leaves and matrices A ∈ Bn(R),
  up to reduction and expansion."

**Definition of `T(G_*)`.** From Zaremsky, *A user's guide to cloning systems*, arXiv:1606.08762,
§5.1 and §5.2, as quoted verbatim in `bit-register-cloning-period-growth-proof`, §0:
- "An expansion of (T−, g, T+) is a triple (U−, h, U+), where U+ is the tree obtained from T+ by
  adding a caret to the kth leaf of T+, for some 1 ≤ k ≤ n, U− is the tree obtained by adding a caret
  to the (ρn(g)k)th leaf of T−, and h = (g)κn_k."
- "[T−, g, T+][U−, h, U+] := [T′−, g′h′, U′+]"
- "the map g ↦ [T, g, T] is a monomorphism Gn ֒→ T(G∗)"
- "T(G∗) also contains Thompson's group F in a natural way, namely as the subgroup of elements of
  the form [T−, 1, T+]."

Trees are finite rooted binary trees, identified with dyadic subdivisions of `[0,1]`. Leaf `i`,
counted from the left, is a standard dyadic interval `[a_i, b_i)`. Here `ρ` is trivial, so an
expansion adds a caret to leaf `k` of **both** trees and replaces `A` by `(A)κ_k`.

**Consequences of the definition used below.** Write `T = T(B_*(R))`.
- **(D1)** `[S, A, S][S, B, S] = [S, AB, S]`, and `[S_1, 1, S_2][S_2, A, S_2][S_2, 1, S_1] = [S_1, A, S_1]`.
  In both products the two middle trees already agree, so no expansion is needed.
- **(D2)** The map `π: T → F`, `[T_-, A, T_+] ↦ [T_-, 1, T_+]`, is a well-defined homomorphism.
  - An expansion changes both trees in the same way whatever `A` is, and `(1)κ_k = 1`.
  - Products expand the same carets whatever the matrices are.
  - `π` restricts to the identity on `F`, and it kills every `[S, A, S]`. So `F ∩ ker π = 1`.
- **(D3)** `F ≤ T` is Thompson's group `F`. `[T_-, 1, T_+]` is the dyadic PL homeomorphism `f` of
  `[0,1]` taking leaf `i` of `T_+` affinely onto leaf `i` of `T_-`, and products are compositions.
  - This is the standard tree-pair model of `F`.
  - Only three facts about it are used:
    - disjointly supported elements commute;
    - `F` is torsion-free;
    - `f` maps dyadic points to dyadic points, standard dyadic intervals to finite unions of them,
      and leaf endpoints of `T_+` to leaf endpoints of `T_-`.
  - Whether `x ↦ f_x` is a homomorphism or an anti-homomorphism depends on conventions, and nothing
    below depends on which. In either case it is injective, and composition of PL maps is
    associative.

## 1. Root-split unipotent blocks are closed under expansion

Fix a tree `S` whose root caret is present (every tree with at least two leaves has one). Let `m`
be the number of leaves of `S` inside `[0,1/2]` and `r` the number inside `[1/2,1]`, with `n = m + r`.
For `X ∈ M_(m×r)(R)` put

`u_S(X) = [[I_m, X], [0, I_r]] ∈ B_n(R)`, and `U(S) = { [S, u_S(X), S] : X ∈ M_(m×r)(R) }`.

By (D1), `u_S(X) u_S(Y) = u_S(X + Y)`, and `U(S) ≅ (M_(m×r)(R), +)` by the monomorphism import.

**Lemma 1.** Let `S'` be `S` with a caret added to leaf `k`. Then
`[S, u_S(X), S] = [S', u_(S')(X'), S']`, where:
- **(a)** if `k ≤ m` (a left leaf), `X'` is obtained from `X` by inserting a zero row as row `k` and
  keeping the old row `k` as row `k+1`;
- **(b)** if `k > m` (a right leaf), `X'` is obtained from `X` by duplicating column `k − m`.

*Proof.* Write `A = u_S(X)` and `B = (A)κ_k`. The entries below the diagonal of `B` are `0`, since
`B ∈ B_(n+1)(R)`. By the block display, row `k` of `B` is `(A_(k,<), A_(k,k), 0, 0) = (0, 1, 0, 0)`.
Every other entry with `i ≤ j` is `A_(π(i), π(j))`, where `π = π_k`.

*(a) `k ≤ m`.* The new tree has `m + 1` left leaves.
- Row `k` of `B` is the unit vector `e_k`.
- Take `i ≠ k` in the new left range `1 ≤ i ≤ m+1`, and `j` in the left range with `i ≤ j`. Then
  `B_(i,j) = A_(π(i),π(j))`. Both indices are at most `m`, so this lies in `I_m`. It is `1` if
  `π(i) = π(j)`, and `0` otherwise.
  - The case `π(i) = π(j)` with `i ≠ j` forces `{i, j} = {k, k+1}`. With `i ≠ k` and `i ≤ j`,
    that is impossible.
  - So this block is `I_(m+1)`.
- For `i ≠ k` and `j ≥ m + 2` (right range), `B_(i,j) = A_(π(i), j−1) = X_(π(i), j−1−m)`.
  Row `k+1` therefore carries old row `k`, and rows `i > k+1` carry old row `i − 1`. Row `k` is
  zero off the diagonal.
- For `i ≥ m + 2`, `B_(i,j) = A_(i−1, j−1)`, which is the `I_r` block. There are no entries in the
  lower-left block, since `i > j` there.

*(b) `k > m`.* The new tree has `r + 1` right leaves.
- Left-range rows `i ≤ m` have `π(i) = i`. Their entries on right columns `j ≥ m+1` are
  `A_(i, π(j)) = X_(i, π(j) − m)`. Columns `k` and `k+1` both equal old column `k`, which is the
  duplication of column `k − m`.
- In the right block, `B_(i,j) = A_(π(i), π(j)) ∈ I_r` for `i ≠ k` and `i ≤ j`. By the argument in
  (a), with `i ≠ k` this is `1` exactly when `i = j`. Row `k` is `e_k`.
- The left block is untouched: `B_(i,j) = A_(i,j)` for `i, j ≤ m`.

So `B = u_(S')(X')`, and the expansion identity is the definition of `T`. ∎

## 2. The limit group `U ≅ R[P] ⊗ LC`

**Notation.**
- `D` is the set of dyadic rationals, and `P = D ∩ (0, 1/2]`.
- `LC` is the free `R`-module of functions `[1/2,1) → R` spanned by the indicators `χ_J` of standard
  dyadic intervals `J ⊆ [1/2,1)`. These are the locally constant functions with finitely many dyadic
  breakpoints.
- `M = R[P] ⊗_R LC`, the module of finitely supported functions `P → LC`.

**The map.** For `S` as in §1, let `b_i` be the right endpoint of left leaf `i` (so `b_m = 1/2`), and
`J_j` the `j`-th right leaf. Put

`Φ_S(X) = Σ_(i,j) X_(i,j) · e_(b_i) ⊗ χ_(J_j) ∈ M`.

**Lemma 2.**
- **(i)** `Φ_S` is an injective additive map.
- **(ii)** `Φ_S(X) = Φ_(S')(X')` in the situation of Lemma 1.
- **(iii)** Every element of `M` is `Φ_S(X)` for some `S` and `X`.

*Proof.*
- **(i)** The `b_i` are distinct points of `P`, and the `χ_(J_j)` are indicators of disjoint nonempty
  intervals. So the elements `e_(b_i) ⊗ χ_(J_j)` are `R`-linearly independent.
- **(ii)**
  - *Case (a).* Leaf `[a, b_k)` splits into `[a, c)` and `[c, b_k)`, with `c` the midpoint. The new
    left endpoints are `c` for row `k`, which is the zero row, and `b_k` for row `k+1`, which is the
    old row. All other rows keep their endpoints.
  - *Case (b).* `χ_J = χ_(J') + χ_(J'')` for the two halves of `J`.
- **(iii)** An element of `M` involves finitely many points of `P` and finitely many dyadic
  intervals. Take `S` fine enough that those points are left-leaf endpoints and those intervals are
  unions of right leaves.

∎

**The subgroup `U`.** Let `U = ∪_S U(S)`, where `S` runs over trees with at least two leaves.
- *`U` is an abelian subgroup.* Any two such trees have a common refinement, reached by a sequence of
  single carets. By Lemma 1, `U(S) ⊆ U(S'')` whenever `S''` refines `S`. So `U` is a directed union
  of the abelian groups `U(S)`.
- *`Φ` is well defined.* Define `Φ: U → M` by `Φ([S, u_S(X), S]) = Φ_S(X)`. Suppose
  `[S_1, u(X_1), S_1] = [S_2, u(X_2), S_2]`. Expand both to a common refinement `S''` using Lemma 1.
  - By the monomorphism import, `G_n → T` is injective, so the two expanded matrices agree.
  - By Lemma 2(ii), `Φ_(S_1)(X_1) = Φ_(S'')(X'') = Φ_(S_2)(X_2)`.
- *Conclusion.* `Φ` is additive by (D1). It is injective by the monomorphism import together with
  Lemma 2(i), and surjective by Lemma 2(iii). So **`U ≅ (M, +)`**.

## 3. `F_L × F_R` acts on `U` by moving points

**The subgroup.** Let `F_(1/2) ≤ F` be the set of elements `x = [S_1, 1, S_2]` such that both trees
have the root caret and the same number of left leaves.
- Equivalently, `f_x` fixes `1/2`.
- Every tree with at least two leaves has the root caret, so `1/2` is a leaf endpoint of both trees.
  `f_x` maps the endpoint with index `m` in the right tree to the one with index `m` in the left
  tree, so `f_x(1/2) = 1/2` exactly when the left-leaf counts agree.
- In particular this includes every element supported in `[0,1/2]` and every element supported in
  `[1/2,1]`.

**Lemma 3.** For `x = [S_1, 1, S_2] ∈ F_(1/2)` and `u ∈ U`: `x u x^(-1) ∈ U`, and
`Φ(x u x^(-1)) = (f_x)_* Φ(u)`. Here `(f_x)_*` is the `R`-linear automorphism of `M` given by

`e_b ⊗ φ ↦ e_(f_x(b)) ⊗ (φ ∘ f_x^(-1))`.

*Proof.*
- **Reduction.** Choose a common refinement `S` of `S_2` and of a tree carrying `u`. Expand `x` so
  that its right tree is `S`, which gives `x = [S*, 1, S]`.
  - The expansion adds the same carets at the same leaf indices to the left tree, so `S*` also has
    the root caret.
  - `f_x` is unchanged: it still takes leaf `i` of `S` affinely onto leaf `i` of `S*`, by (D3).
  - Both trees have the same number `m` of left leaves.
- **Conjugation.** Write `u = [S, u_S(X), S]`. By (D1),
  `x u x^(-1) = [S*, 1, S][S, u_S(X), S][S, 1, S*] = [S*, u_(S*)(X), S*] ∈ U`. The same matrix works
  because the left/right leaf counts agree.
- **Transport.** `f_x` maps leaf `i` of `S` onto leaf `i` of `S*`. So it sends `b_i(S) ↦ b_i(S*)`,
  and `χ_(J_j(S)) ∘ f_x^(-1) = χ_(J_j(S*))`. Hence `Φ_(S*)(X) = (f_x)_* Φ_S(X)`.
- **Well-definedness of `(f_x)_*`.** `f_x` preserves `(0,1/2]` and `[1/2,1)` and maps `D` to `D`.
  It maps each standard dyadic interval to a finite union of standard dyadic intervals, so
  `φ ∘ f_x^(-1) ∈ LC`.

∎

## 4. Jump basis

**Lemma 4.** `LC` is free on `{1} ∪ {χ_[c,1) : c ∈ D ∩ (1/2, 1)}`. If `f` is an increasing dyadic PL
homeomorphism of `[1/2,1]`, then `χ_[c,1) ∘ f^(-1) = χ_[f(c),1)` and `1 ∘ f^(-1) = 1`.

*Proof.*
- *Spanning.* A function `φ ∈ LC` has finitely many breakpoints `c_1 < … < c_s` in `D ∩ (1/2,1)`,
  and it is constant between them. So `φ = φ(1/2) · 1 + Σ_t (φ(c_t) − φ(c_t^-)) χ_[c_t,1)`.
- *Independence.* Evaluate a relation at points just to the right of each `c` in turn. Also
  `χ_J = χ_[c,1) − χ_[d,1)` for `J = [c, d)`, with `χ_[1/2,1) = 1` and `χ_[1,1) = 0`, so the two
  bases span the same module.
- *Transport.* `f` is increasing, so `f^(-1)(x) ≥ c` iff `x ≥ f(c)`.

∎

So `M` contains the free `R`-module `M' = R[P × D_R]`, where `D_R = D ∩ (1/2,1)`, with basis
`E_(b,c) = e_b ⊗ χ_[c,1)`. For `f ∈ F_(1/2)`, Lemmas 3 and 4 give

`(f)_* E_(b,c) = E_(f(b), f(c))`.

## 5. The wreath product

**The top group.** Choose, via (D3), the following elements of `F_(1/2)`:
- `g = [S_1, 1, S_2]` with `S_2 = {[0,1/8), [1/8,1/4), [1/4,1/2), [1/2,1)}` and
  `S_1 = {[0,1/4), [1/4,3/8), [3/8,1/2), [1/2,1)}`. Its map `f_g` is supported in `[0,1/2]` and
  sends `1/8 ↦ 1/4 ↦ 3/8`.
- `h = [S_3, 1, S_4]` with `S_4 = {[0,1/2), [1/2,5/8), [5/8,3/4), [3/4,1)}` and
  `S_3 = {[0,1/2), [1/2,3/4), [3/4,7/8), [7/8,1)}`. Its map `f_h` is supported in `[1/2,1]` and
  sends `5/8 ↦ 3/4 ↦ 7/8`.

**Properties of the top group.**
- *Infinite orbits.* On `[1/4,1/2]` the map is `f_g(t) = t/2 + 1/4`, whose only fixed point there is
  `1/2`. So the orbit of `x_0 = 1/4` accumulates at `1/2` and is infinite. Symmetrically the orbit of
  `y_0 = 3/4` under `f_h` is infinite. So `i ↦ f_g^i(1/4)` and `j ↦ f_h^j(3/4)` are injective on `Z`.
- *`Z^2`.* `f_g` and `f_h` have disjoint supports and commute, so `g h = h g` by (D3). If
  `g^i h^j = 1`, restrict the PL map to `[0,1/2]` to get `f_g^i = id`, so `i = 0`; likewise `j = 0`.
  So `Q = ⟨g, h⟩ ≅ Z^2`.

**The lamps.**
- *Definition.* For `λ ∈ R`, let `a_λ = Φ^(-1)(λ E_(1/4, 3/4)) ∈ U`. Concretely,
  `a_λ = [S, u_S(X), S]` with `S = {[0,1/4), [1/4,1/2), [1/2,3/4), [3/4,1)}` and
  `X = [[0, λ], [0, 0]]`.
- *Conjugates.* Let `w = g^i h^j`, and write `c_w(u) = w u w^(-1)`. Then `c_w = c_g^i c_h^j`. By
  Lemma 3 applied to `g^(±1)` and `h^(±1)`, and Lemma 4:

  `Φ(c_w(a_λ)) = λ E_(x_i, y_j)`, where `x_i = f_g^(±i)(1/4)` and `y_j = f_h^(±j)(3/4)`,

  with one fixed choice of sign on each coordinate, depending on conventions. The points
  `(x_i, y_j)` are pairwise distinct for distinct `(i, j)`, by the infinite orbits above.
- *The base group.* Let `B = ⟨ c_w(a_λ) : w ∈ Q, λ ∈ R ⟩ ≤ U`. By Lemma 2 and Lemma 4, `Φ` maps
  `B` isomorphically onto `⊕_((i,j) ∈ Z^2) R · E_(x_i, y_j)`, and this is `⊕_(Z^2) (R, +)`.
- *The action.* Conjugation by `g` or `h` shifts one index. So `Q` acts on `B` by the regular
  permutation of coordinates.

**Conclusion.**
- `Q` normalizes `B` (Lemma 3).
- `B ∩ Q ⊆ ker π ∩ F = 1` by (D2).
- Hence `⟨B, Q⟩ = B ⋊ Q ≅ (⊕_(Z^2) R) ⋊ Z^2 = (R, +) ≀ Z^2`.

**Special cases.**
- Restricting to `λ ∈ Z · 1` gives `(Z · 1) ≀ Z^2`. That is `Z ≀ Z^2` in characteristic 0, and
  `F_p ≀ Z^2` in characteristic `p`.

∎

## Numerical cross-check

`lamplighter_in_upper_triangular_cloning.py` implements `T(B_*(F_3))` with the pure expansion and
product rules above. It checks:
- the Figure 6 example;
- `(C1)`, `(C2)` (including `ℓ = k`) and compatibility `(2)` for `n ≤ 5`;
- Lemma 1 and Lemma 2(ii) on 360 random expansions;
- with the elements `g`, `h`, `a = a_1` above:
  - `[g, h] = 1` and `a^3 = 1`;
  - `Φ(w a w^(-1)) = E_(x_i, y_j)` for all `|i|, |j| ≤ 3`, with the product structure in `(i, j)` and
    no repeated points;
  - pairwise commutation of sampled conjugates.

The orbits printed in `output.txt` are `x_i ∈ {1/32, …, 1/4, 3/8, 7/16, 15/32}` and
`y_j ∈ {17/32, …, 3/4, 7/8, 15/16, 31/32}`.
