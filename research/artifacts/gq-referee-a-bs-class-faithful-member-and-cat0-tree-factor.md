# Referee report (gq-referee-a, proof-gap lens): the BS-class faithful member, arithmetic NSP members, and the CAT(0) tree factor

**Reviewed** (lane bh-cat0, 61db7e38a), read on origin/main:
- `bs-class-faithful-member-type-a-proof`, which targets `bs-class-with-faithful-member-lies-in-type-a-class`;
- `arithmetic-nsp-faithful-bs-member-proof`, which targets `arithmetic-nsp-lattices-have-faithful-bs-members`;
- `cat0-tree-factor-type-a-proof`, which targets `cat0-groups-with-a-tree-factor-lie-in-type-a-class`.

**Verdict: PASS for all three.** I found no gap in the steps the author asked about. There are three nits, one per
route. The following are cited and for the citation lens:
- the BLIW §§10–12 inputs;
- the normal subgroup theorems;
- strong approximation;
- Bieberbach;
- Foertsch–Lytchak;
- Bridson–Haefliger III.Γ.1.1.

## 1. The gluing step (`bs-class-faithful-member-type-a-proof`, Step 1)
- *`L ∈ BS_G`.* The new edge group `A_0 ≅ B_0` has finite index in both `A` and `B`, so `L ∈ BS_G`.
- *The subgraphs inject.* `K ≤ L` and `H ≤ L`. The Bass–Serre tree of the connected subgraph of groups `H_Γ` embeds
  `H`-equivariantly in `T_L`, as the subtree spanned by the `H`-orbit of a lift of `H_Γ`.
- *The kernel.* The kernel `N` of `L` fixes the vertex `w` with `L_w = B`, so `N ≤ B ≤ H`. `N` fixes that subtree
  pointwise, and it is `H`-isomorphic to `T_H`. So `N ≤ ker(H ↷ T_H) = 1`. ✓
- *The rest.* Vertex groups commensurable with the finitely presented `G` are finitely presented. Then the faithful
  type (A) theorem and subgroup-closure of `B_A` apply. ✓
- **N1.** Say "connected subgraph of groups" for `H_Γ`. The equivariant embedding of trees needs connectedness, which
  holds here.

## 2. The lemma and both instances (`arithmetic-nsp-faithful-bs-member-proof`)
- **The lemma.**
  - *`H_c ∈ BS_G`.* `c` commensurates `G`, so `G_1` and `cG_1c^(−1) = G ∩ cGc^(−1)` have finite index.
  - *`K` is `c`-invariant.* `K` is the core of `G`, since all vertices form one orbit.
    - Britton's lemma gives `G ∩ t^(−1)Gt = G_1`, so `K ≤ G_1`.
    - `tkt^(−1) = ckc^(−1)` for `k ∈ G_1`, so `cKc^(−1) = K`. ✓
  - *`M = N_L(K)` is closed.* `K` is discrete, hence closed. So limits of `g_jkg_j^(−1) ∈ K` stay in `K`, and the same
    holds for `g^(−1)`.
  - *`M` is countable.* By (C) the kernel of `M → Aut(K)` is `C_M(K) = 1`, and `Aut(K)` is countable for finitely
    generated `K`.
  - *`M` is discrete.* By Baire, a countable locally compact second countable group is discrete.
  - *The conclusion.* `M ⊇ K`, a lattice, so `[M:K] < ∞`, hence `c^m ∈ K ⊆ G`, a contradiction. ✓
- **Instance 1** (`SL_n(Z)`, `n ≥ 3`).
  - *(N).* Margulis, and a torsion-free group has trivial central subgroups.
  - *(C).* A finite-index `N` contains some `x_ij(k)`, whose Zariski closures are the root groups. So `N` is Zariski
    dense in `SL_n` (N2).
  - *`c` has no power in `G`.* If `c^m = λA` with `A ∈ G`, then `λ^(−1) ∈ Z`, from the `(2,2)` entry, and
    `λ^n = r^m`. That gives `r^m ≤ 1`, a contradiction. ✓
- **Instance 2** (definite quaternion algebra, primes `p, q`): the Bader–Shalom hypotheses for the closures `G_i`.
  - *Non-discrete.* A vertex stabilizer of `G` in the other tree is infinite, and it projects injectively into a
    compact open subgroup.
  - *`PSL_2(Q_p) ≤ G_p ≤ PGL_2(Q_p)`.*
    - Strong approximation for `SL_1(D)` with respect to `{q}` makes `SL_1(O[1/pq])` dense in `SL_2(Q_p)`.
    - Its intersection with `G` has finite index, so its closure is a closed subgroup of finite index.
    - `PSL_2(Q_p)` is abstractly simple, so it lies in `G_p`.
    - So `G_p` is open, of finite index in `PGL_2(Q_p)`, and compactly generated.
  - *Just-non-compact, with no abelian normal subgroup.* Let `1 ≠ N ⊴ G_i` be closed.
    - If `N ∩ PSL_2 = 1`, then `[N, PSL_2] = 1`, and the centralizer of `PSL_2` in `PGL_2` is trivial.
    - So `N ⊇ PSL_2`, and `G_i/N` is finite.
  - *The lattice.* `Γ = G` is cocompact in `G_p × G_q`, because it is cocompact in the larger `PGL_2 × PGL_2` and
    contained in `G_p × G_q`. Its projections are dense by definition of `G_i`.
  - These match the quoted Bader–Shalom statement with `n = 2`. So `G` is just-infinite. ✓
  - *(C).* A finite-index `N` contains a nonabelian free group. Proper algebraic subgroups of `PGL_2` are virtually
    solvable, so `N` is Zariski dense in each factor, with trivial centralizer. ✓
  - *The element `c`.*
    - `D^×(Q)` is dense in `GL_2(Q_r)`, and hyperbolicity is open, so a hyperbolic rational `c` exists.
    - `G ⊆ (O ⊗ Z_r)^×` is elliptic on `T_r`, while `c^m` is hyperbolic. Scalars act trivially on `T_r`, so `c^m ∉ G`
      in `L`. ✓
- **N2 (Instance 1, (C)).** In `PGL_n`, "`ḡ` centralizes `N̄`" means `gxg^(−1) = λ(x)x` in `GL_n`, and `λ(x)^n = 1`, so
  `λ` takes values in `{±1}`. Add the line: `ker λ` has index at most 2, is still Zariski dense by the same root-group
  argument, and so `g` is scalar.

## 3. Fibre cocompactness and instance (a) (`cat0-tree-factor-type-a-proof`)
- **Step 1.** `pr_T(C)` is compact in the locally finite `T`, so it meets finitely many vertices. That gives finitely
  many orbits of vertices, and hence of edges.
  - With the barycentric subdivision, the action is without inversions.
  - Orbit–stabilizer gives `[Γ_v : Γ_e] ≤ deg v`. ✓
- **Step 2, cocompactness of `Γ_v` on `F_v` (the author asked about this).** Take `x ∈ F_v` with `x = γk`, `k ∈ C`.
  - Then `pr_T(k) = γ^(−1)v` is a vertex `w_j` of `pr_T(C)` in `Γv`.
  - So `h = γg_j^(−1)` fixes `v`, and `x = h·g_jk` with `k ∈ C ∩ F_(w_j)`, a closed subset of a compact set.
  - So `F_v = Γ_v·⋃_j g_j(C ∩ F_(w_j))` is a finite union of translates of compact sets. The action is proper by
    restriction. ✓
- **The rest of Step 2.** A geometric CAT(0) action gives finite presentation. Commensurability propagates along
  the connected `T'`, so `Γ ∈ BS_(Γ_v)`. ✓
- **Instance (a), degenerate trees.** A connected tree with all degrees at most 2 is a finite path, a ray or a line.
  - A ray: its only isometry is the identity, so `Y × ray` has no cocompact action.
  - A line: `Γ` acts geometrically on `E^(n+1)`.
  - A finite path: `Γ` fixes the center, which is a vertex of `T'`, and acts geometrically on that fibre.
  - Either way `Γ` is virtually `Z^k`, hence linear. ✓
- **Instance (a), non-degenerate trees.**
  - A branching `T` has no Euclidean de Rham factor, so isometries split. This is cited.
  - *The fibre group.* Let `G' = ` the preimage of the Bieberbach lattice, a finite-by-`Z^n` group.
    - The centralizer of the finite kernel has finite index, and it is a central extension by the finite `Z(F)`.
    - So it is finitely generated nilpotent, hence virtually torsion-free.
    - A torsion-free finite-index subgroup meets `F` trivially and embeds with finite index in `Z^n`. So `G` is
      commensurable with `Z^n`. ✓
  - *The faithful member.* In the ascending HNN extension `tZ^nt^(−1) = 2Z^n`, the kernel lies in
    `⋂_i t^iZ^nt^(−i) = ⋂ 2^iZ^n = 0`. So it is faithful, and it lies in `BS_(Z^n)`. ✓
- **Instance (a), `n = 0`.** `G` is finite, so `Γ` is virtually free, hence linear. ✓
- **N3 (Step 2).** Name the reason `Γ_v` preserves `F_v`: `γ = (γ_Y, γ_T)` with `γ_T v = v`. Note that the degenerate
  finite-path case uses the center of `T'`, which may be a midpoint of `T`.
