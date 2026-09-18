# Referee report (gq-referee-a, proof-gap lens): commensurator-rigid BS classes are virtual products, and CAT(0) groups on symmetric space × tree

**Reviewed** (lane bh-cat0), the current versions at 8200dc09a, read on origin/main:
- `commensurator-rigid-bs-products-proof`, which targets `commensurator-rigid-bs-classes-are-virtual-products`. It now
  consumes `commensurator-rigid-groups-have-no-faithful-bs-members` and covers every member of `BS_G`, torsion
  included.
- `cat0-symmetric-space-tree-type-a-proof`, which targets `cat0-groups-on-symmetric-space-times-tree-lie-in-type-a-class`.

**Verdict.**
- **The products node: PASS.**
- **The CAT(0) node: PASS**, with one required scope fix (W1), for the case where `T` is a line.
- There is one nit.
- For the citation lens: Mostow–Prasad, Borel density, Bass–Serre, Foertsch–Lytchak, and Kazhdan–Margulis inside the
  Hecke node.

## 1. `commensurator-rigid-bs-products-proof`
- **Step 1.**
  - By the no-faithful-member node, a finite-index subgroup of `G_v` lies in `K`. Also `K ⊆ G_x` for every `x`, so
    `[G_x : K] < ∞` at every vertex, by conjugation.
  - `G_v` is finitely generated, because it is commensurable with the finitely generated `G`.
  - `H/K` acts faithfully with finite stabilizers and finitely many orbits, so it is virtually free and finitely
    generated. ✓
- **Step 2: `VZ(K)` finite (the author asked about this).**
  - `VZ(K) ∩ U = VZ(U)`, since finite-index subgroups of `U` and of `K` are mutually cofinal.
  - `VZ(U) ≅ VZ(U') ⊆ VZ(G) = ker κ_G = 1`.
  - `aU = bU` with `a, b ∈ VZ(K)` gives `a^(−1)b ∈ VZ(K) ∩ U = 1`, so `|VZ(K)| ≤ [K : U]`. ✓
- **Step 3: `Out(K)` finite (the author asked about this).**
  - *The kernel.* For `α ∈ ker κ` and `x ∈ K_0 ∩ n^(−1)K_0n`: `α(n)xα(n)^(−1) = α(nxn^(−1)) = nxn^(−1)`. So
    `n^(−1)α(n) ∈ VZ(K)`, and `α` is fixed by finitely many choices on a finite generating set.
  - *The image.* `κ_K(U)` corresponds to `κ_G(U')` under `Comm(K) ≅ Comm(G)`, and it has finite index.
  - *The bound.* `[Aut : Inn] ≤ [κ(Aut) : κ(Inn)] · [Inn·ker κ : Inn] < ∞`. ✓
- **Step 4 (the author asked about this).**
  - `H_2 = K·C`, and `K ⊆ H_2`.
  - `Z(K)` is central in `C` and lies in `C`.
  - Freeness of `Φ` splits the extension.
  - `F ∩ K ⊆ F ∩ Z(K) = 1`.
  - `[C_1 : F] = |Z(K)|`, so `[H_2 : KF] ≤ [C : C_1][C_1 : F] < ∞`. ✓
- **Step 5.** `K_0 × F` has finite index in `H`, and the closure node gives `H ∈ B_A`. ✓
- **The instances.**
  - Mostow–Prasad applies for irreducible `X ≠ H^2`.
  - A discrete subgroup of `Isom(X)` containing the lattice `G` contains it with finite index.
  - `VZ(G) = 1` by Borel density.
  - Linearity comes via the adjoint representation. ✓

## 2. `cat0-symmetric-space-tree-type-a-proof`
- **Step 1.**
  - `G_0` is torsion-free and acts properly, so it acts freely, hence faithfully. It is a cocompact lattice in the
    simple centerless `Isom(X)^0`.
  - `BS_G = BS_(G_0)`.
  - The target's "`Γ_v` residually finite ⇒ virtually torsion-free" is right: the kernel of `Γ_v → Isom(X)` is
    finite, and Selberg applies to the image. ✓
- **The dichotomy never uses Margulis's arithmeticity or commensurator theorems (the author asked me to attack
  this).** The split is on the discreteness of `Comm_L(G_0)` itself.
  - **2a** uses only non-discreteness. Inside the Hecke node, finding finitely many `c_i` with `⟨G, c_i⟩`
    non-discrete uses the Kazhdan–Margulis covolume bound, which is not the arithmeticity or commensurator theorem.
    That node is refereed PASS.
  - **2b** uses Mostow–Prasad and Borel density only.
  - The paragraph "Which case occurs" is correctly marked as unused. So (i) holds. ✓
- **2b and 2c.**
  - Item 3 of the products node needs a finite-index subgroup of `G_0` in `B_A`, which `G_0` itself supplies.
  - `X = H^2` goes to the refereed `H^2 × T` node. ✓

## Required fix
- **W1 (the CAT(0) node: the line case of "preserved automatically").**
  - The product decomposition is preserved when `T` is a line. But Step 1 goes through Bass–Serre (item 1 of
    `cat0-groups-with-a-tree-factor-lie-in-type-a-class`), and that needs `Γ` to act on `T` by tree automorphisms.
  - With a branch point this is automatic: vertices are exactly the points at integer distance from a branch vertex,
    and isometries map branch vertices to branch vertices. Subdivide to remove inversions.
  - For `T = R`, the translation part can be dense. Take a lattice `G ≤ Isom(H^3)` with `φ : G → R` of image `Z + √2Z`.
    Then `Γ = {(g, φ(g) + n)}` acts properly and cocompactly on `H^3 × R`, but not simplicially, and "the vertex
    stabilizers `Γ_v`" are undefined.
  - The conclusion still holds there, by a direct argument:
    - the kernel of `Γ → Isom(X) × Isom(R)` is finite, by properness;
    - the target group is linear in characteristic 0;
    - so a torsion-free finite-index subgroup is linear, and `Γ ∈ B_A` when `Γ` is virtually torsion-free.
  - Either add this argument for the line case, with hypothesis "`Γ` virtually torsion-free", or restrict the
    statement to actions by automorphisms of `T`.

## Nit
- **N1 (products node, Step 1).** Say "`[G_x : K] < ∞` for every vertex `x` of the tree, not only `v`". The
  finite-stabilizer claim for `H/K` needs it. It holds because every vertex group is conjugate to one of finitely many
  `G_v`, and `K` is normal.
