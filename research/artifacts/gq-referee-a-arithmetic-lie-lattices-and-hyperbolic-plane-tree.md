# Referee report (gq-referee-a, proof-gap lens): faithful BS members for arithmetic Lie lattices, and H^2 × tree

**Reviewed** (lane bh-cat0, a732dc8b6), read on origin/main:
- `arithmetic-lie-lattices-faithful-bs-proof`, which targets `arithmetic-lie-lattices-have-faithful-bs-members`;
- `cat0-hyperbolic-plane-tree-type-a-proof`, which targets
  `cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class`.

**Verdict: PASS for both.** The key claim holds: the lemma uses no normal subgroup theorem, so it covers rank-one
arithmetic lattices, surface groups included. There are three nits. The inputs listed in the trust surfaces are for
the citation lens.

## 1. `arithmetic-lie-lattices-faithful-bs-proof`
- **Step 1.** `K = core_H(G)`, because there is one vertex orbit. By Britton, `K ≤ G ∩ t_i^(−1)Gt_i = G_i`. With
  `t_ikt_i^(−1) = c_ikc_i^(−1)`, this gives `c_iKc_i^(−1) = K`. So `D` normalizes `K`. ✓
- **Step 2.** `K` is discrete, hence closed. So `N_L(K)` is closed and contains `D̄`. ✓
- **Step 3.**
  - A closed non-discrete subgroup of a Lie group has positive dimension, so `D̄° ≠ 1`.
  - `g ↦ gkg^(−1)` maps the connected `D̄°` into the discrete `K`, so it is constant, and `D̄°` centralizes `K`.
  - `d = Lie(D̄°)` is `Ad(D̄)`-invariant, hence `Ad(G)`-invariant.
  - The stabilizer of a subspace is algebraic, and Borel density makes `Ad(G)` Zariski dense in `Ad(L)`. So `d` is an
    ideal, and it contains a simple ideal `l_j`. Hence `L_j ≤ D̄°` centralizes `K`. ✓
- **Step 4.**
  - `Z_L(L_j) = ∏_(i≠j)L_i`, because `L_j` is centerless.
  - For `k = 1`, `K ⊆ Z(L) = 1`.
  - For `k ≥ 2`, irreducibility makes `K ⊆ G ∩ ∏_(i≠j)L_i` finite. A finite normal subgroup of the Zariski-dense `G`
    is normalized by `L`, and a connected group acts trivially on a finite group. So `K ⊆ Z(L) = 1`. ✓
- **The key claim (the author asked me to attack it).** Nothing in Steps 1–4 uses a normal subgroup theorem.
  - The only inputs are non-discreteness of `D`, Borel density and irreducibility.
  - For `L = PSL_2(R)`, `k = 1`, so Step 4 is immediate. The lemma therefore covers cocompact arithmetic Fuchsian
    groups, and it covers surface groups through them. I found no hidden use of just-infiniteness. ✓
- **Step 5.**
  - *Countability of `Comm_L(G)`.* An element `c` is determined by the isomorphism `G_c → cG_cc^(−1)` it induces. Two
    elements inducing the same isomorphism differ by an element of `Z_L(G_c)`, which is `Z(L) = 1` by Borel density.
    `G` is finitely generated, so there are countably many such isomorphisms. ✓
  - *The chain.*
    - If every `D_r` is discrete, it is a lattice with `[D_r : G] = covol(G)/covol(D_r) ≤ covol(G)/ε`, by
      Kazhdan–Margulis.
    - A chain of subgroups of bounded index over `G` stabilizes, so `Comm_L(G) = D_R` would be discrete.
    - So some `D_r` is non-discrete. ✓
  - *The transfer.* `BS_G` depends only on the commensurability class. `G` is finitely presented, as a lattice, and
    the bs-class node applies. ✓
- **Instances.**
  - The quaternion algebra ramified at `{2,3}` is indefinite, so `O^1/±1 ≤ PSL_2(R)` is cocompact and arithmetic.
    Its torsion-free finite-index subgroup is a closed surface group, and all genera `≥ 2` are commensurable.
  - `PSL_2(Q)` is a dense commensurator for free subgroups of `PSL_2(Z)`.
  - The non-arithmetic exclusion is correct: by Margulis the commensurator is then a lattice, so every `D` is
    discrete. ✓
- **N1 (Step 4).** The finite-`K` argument works for every `k`. You could state it once. Say that "Zariski closed"
  refers to `Ad(L)` as the identity component of a real algebraic group.

## 2. `cat0-hyperbolic-plane-tree-type-a-proof`
- **The fibre group is virtually a surface group (the author asked about this).**
  - `F = ker(G → Isom(H^2))` is finite, by properness. The image `Q` is a cocompact discrete group.
  - Selberg gives a torsion-free finite-index subgroup. Pass to its orientation-preserving part, of index at most 2, to
    get a closed orientable surface group `S` (N2).
  - In the preimage `E` of `S`, `C = C_E(F)` has finite index, and `C ∩ F = Z(F) =: A` is central in `C`. So
    `1 → A → C → S' → 1` is central, with `S'` a surface group.
  - The extension class lies in `H^2(S'; A) ≅ Hom(H_2(S'), A) = A`, since `H_1` is free. Restriction to a cover of
    degree `|A|`, which exists, multiplies it by `|A|`, so the class dies.
  - The pulled-back extension then splits, and `G` contains `S''` with finite index. ✓
- **Degenerate trees.** Degree at most 2 means a finite path, a ray or a line. The ray is impossible, as in the
  tree-factor node (N2).
  - A line gives a geometric action on `H^2 × R`, which is virtually `S × Z` (Scott, cited).
  - A finite path gives a geometric action on the central fibre, which may sit over a midpoint.
  - Either way `Γ` is linear in characteristic zero (N3). ✓
- **The branching case.** Foertsch–Lytchak (cited) preserves the factors, and `γ_Tv = v` preserves the fibre. The
  tree-factor node gives `Γ ∈ BS_G`, and instance 1 of the Lie node gives `BS_G ⊆ B_A`. ✓
- **Item 2.**
  - Residual finiteness of `G` gives a finite-index `G_0` with `G_0 ∩ F = 1`, isomorphic to a finite-index subgroup of
    `Q`.
  - `Q ∩ Isom(X)^0` has finite index in `Q`, and it is an irreducible arithmetic lattice in the centerless
    `L = Isom(X)^0`, which has no compact factors.
  - So `G ~ Q ∩ L` are commensurable, and `BS_G = BS_(Q∩L) ⊆ B_A`.
  - The reducible case is correctly excluded. ✓
- **N3 (degenerate case).** "Linear over `Z`" is true, but it needs a line of proof: an arithmetic commensurable
  surface group, via restriction of scalars, and then induced representations. Otherwise say "linear over a field of
  characteristic 0", which is what `char-zero-linear-groups-satisfy-permutational-boone-higman` uses.
- **N2.** Pass to orientation-preserving elements before invoking the surface-group structure, since `Q` may contain
  reflections. Mention the ray in the degree-at-most-2 trichotomy.
