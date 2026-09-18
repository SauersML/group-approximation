---
rg: 2
id: arithmetic-nsp-faithful-bs-member-proof
kind: route
title: A nontrivial kernel would be a finite-index subgroup normalized by c, and a countable normalizer is discrete
target: arithmetic-nsp-lattices-have-faithful-bs-members
requires: [higher-rank-lattice-normal-subgroups-central-or-finite-index, bader-shalom-normal-subgroup-theorem]
---

**Lemma.** `c` commensurates `G`, so `G_1` and `c G_1 c^{-1} = G ∩ cGc^{-1}` have
finite index in `G`. So `H_c` is an HNN extension with vertex group `G`, edge group
`G_1`, and both edge inclusions of finite index, which puts `H_c` in `BS_G`.

Let `K` be the kernel of `H_c` on its Bass--Serre tree. Vertex stabilizers are the
conjugates of `G`, so `K` is the largest normal subgroup of `H_c` contained in `G`.
- `K <= G ∩ t^{-1} G t = G_1` (Britton's lemma), and `t K t^{-1} = K`. Since
  `t k t^{-1} = c k c^{-1}` for `k ∈ G_1`, this gives `c K c^{-1} = K` inside `L`.
- `K` is normal in `G`. By (N), `K = 1`, or `K` has finite index in `G`.

Suppose `[G : K] < ∞`, and let `M = N_L(K) = {g ∈ L : gKg^{-1} = K}`. Then:
- `M` is closed. If `g_j → g` with `g_j ∈ M` and `k ∈ K`, then `g_j k g_j^{-1} ∈ K`
  converges, and `K` is discrete, so `gkg^{-1} ∈ K`; the same holds for `g^{-1}`.
- `M` is countable. By (C), conjugation `M → Aut(K)` is injective, and `K` is
  finitely generated, as a finite-index subgroup of `G`, so `Aut(K)` is countable.
- A countable closed subgroup of a locally compact, second countable group is
  discrete (Baire).
- So `M` is a discrete subgroup containing the lattice `K`, and `[M : K] < ∞`.

Since `c ∈ M`, some `c^m`, `m >= 1`, lies in `K <= G`. This is a contradiction, so
`K = 1`.

**Instance 1.** Let `L = PGL_n(R)` and `G <= SL_n(Z)` torsion-free of finite index.
`G` meets the finite center trivially, so it maps injectively to `L` as a lattice.
- (N): `higher-rank-lattice-normal-subgroups-central-or-finite-index` (its general
  statement; its "form used" paragraph treats `Sp_2n` only). `SL_n(Z)` is an
  irreducible lattice in the simple group `SL_n(R)` of real rank `n-1 >= 2`. For
  `SL_n(R)` of real rank `n-1 >= 2`. A central normal subgroup of the torsion-free
  `G` is trivial.
- (C): a finite-index `N <= G` contains `x_ij(k)` for some `k >= 1` and all
  `i ≠ j`. Their Zariski closures are the full root groups, which generate `SL_n`.
  So `N` is Zariski dense. If `g ∈ PGL_n(R)` centralizes `N`, a lift satisfies
  `g x g^{-1} = λ(x) x` with `λ(x) = ±1`. So `g` centralizes `ker λ`, which has index
  `<= 2` in `N` and is still Zariski dense, and `g` is trivial in `PGL_n(R)`.
- `c = diag(r,1,...,1)` commensurates `SL_n(Z)`. If `c^m = λA` in `GL_n(R)` with
  `A ∈ SL_n(Z)`, then comparing entries gives `λ^{-1} ∈ Z` and `λ^n = r^m`. That
  forces `|λ| <= 1` and `r^m <= 1`, which is false for `m >= 1`.

**Instance 2.** `Λ` is a cocompact lattice in `L = PGL_2(Q_p) × PGL_2(Q_q)`
(cocompactness of definite quaternion S-arithmetic groups: the compactness criterion
for Q-anisotropic groups; not pinned at source). `G` is then a cocompact lattice in
the open subgroup `G_1 × G_2` of `L`, as the Bader--Shalom node requires: `D` is
definite, so the archimedean factor is compact. The diagonal map
`PD^×(Q) → PGL_2(Q_p)` is injective.
- (N): `bader-shalom-normal-subgroup-theorem` with `n = 2` and `G_i` the closures of
  the two projections of `G`.
  - Each `G_i` is non-discrete: a vertex stabilizer of `G` in the other tree is
    infinite and projects injectively into a compact vertex stabilizer.
  - Each `G_i` contains `PSL_2(Q_p)` (resp. `PSL_2(Q_q)`). By strong approximation
    for `SL_1(D)` with respect to `S = {∞, q}` (Rapinchuk, arXiv:1207.4425, Thm 2.3,
    p. 12; `SL_1(D)(R)` is compact, so `∞` may be added to `S`), `SL_1(O[1/pq])` is dense in
    `SL_1(D)(Q_p) = SL_2(Q_p)`. The part of it lying in `G` has finite index, so its
    closure has finite index in a closed group mapping onto `PSL_2(Q_p)`, and
    `PSL_2(Q_p)` is simple, hence has no proper finite-index subgroup.
    So `PSL_2(Q_p) <= G_i <= PGL_2(Q_p)`, and `G_i` is open and compactly generated.
  - Let `1 ≠ N` be closed and normal in `G_i`. If `N ∩ PSL_2(Q_p) = 1`, then `N`
    centralizes `PSL_2(Q_p)`, whose centralizer in `PGL_2(Q_p)` is trivial. So
    `N ⊇ PSL_2(Q_p)` and `G_i / N` is finite. Hence `G_i` is just-non-compact and
    has no nontrivial abelian normal subgroup.
  - Hence `G` is just-infinite, which is (N).
- (C): a finite-index `N <= G` contains a non-abelian free subgroup (the stabilizer
  of a vertex of `T_q` acts properly and cocompactly on `T_p`). Proper algebraic
  subgroups of `PGL_2` are virtually solvable, so `N` is Zariski dense in each
  factor and has trivial centralizer.
- `c`: `D^×` is open in the affine space `D`, so `D^×(Q)` is dense in
  `D^×(Q_r) ≅ GL_2(Q_r)`, and hyperbolicity on `T_r` is an open condition; such a
  `c` exists. Every element of `D^×(Q)` commensurates `O[1/pq]^×`. `G` lies in the
  image of `(O ⊗ Z_r)^×`, a maximal compact subgroup fixing a vertex of `T_r`, so
  every element of `G` is elliptic on `T_r`. Every power `c^m` is hyperbolic, so
  `c^m ∉ G`.

**Trust surface.** Cited and not re-read:
- the normal subgroup theorems, through the two nodes named above;
- strong approximation for `SL_1(D)`, pinned by referee b to Rapinchuk arXiv:1207.4425
  Thm 2.3;
- cocompactness of definite quaternion S-arithmetic groups;
- Britton's lemma;
- the fact that a discrete subgroup containing a lattice contains it with finite index.
