---
rg: 2
id: commensurated-cat0-witnesses-force-finite-rational-cd-proof
kind: route
title: "Proof: a compact open K fixes a point of X, so the fixed set Z of rho(N) is a nonempty convex subcomplex on which F/N acts with stabilizers injecting into G_z/(G_z cap K); the cellular chains of Z are a length-d projective resolution of Q over Q[F/N]"
target: commensurated-cat0-witnesses-force-finite-rational-cd
requires:
  - commensurated-witnesses-survive-browder-but-die-when-linear
---

Verification tier: proposed-established. Standard inputs:
- Bridson–Haefliger, *Metric spaces of non-positive curvature*: I.7 (an
  `M_κ`-polyhedral complex with finitely many shapes is a complete geodesic
  space), II.2.7–2.8 (bounded sets in complete CAT(0) spaces have unique
  circumcentres; bounded orbits give fixed points), II.2 (convex subsets are
  contractible by geodesic homotopy).
- Brown, *Cohomology of Groups*, VIII.2 and VIII.11 (a projective resolution
  from a proper cellular action; free actions on contractible complexes).
- Bruhat–Tits: the extended building of `GL_d(k)`, `k` non-archimedean local
  (any characteristic), is a locally finite Euclidean polyhedral complex with
  finitely many shapes, CAT(0), with compact open point stabilizers.

Notation: `π : F -> P = F/N`, `ρ : F -> G`, `N = F ∩ ρ^{-1}(K)`.

## Step 0: subdivision

Replace `X` by its barycentric subdivision `X'`. Its vertices are the
barycentres of cells of `X`, its simplices are flags. `G` acts on `X'` by
simplicial isometries. An element stabilizing a simplex of `X'` preserves the
dimension of the cells indexing its vertices, so fixes every vertex, and acts
as the identity on the simplex (it is affine there). So the action is
**without inversions**. A vertex stabilizer in `X'` is a cell stabilizer in
`X`, hence compact open; a simplex stabilizer is a finite intersection of
these. `X'` is still locally finite, CAT(0), of dimension `d`, with finitely
many shapes.

For any subgroup `S ≤ G`, `Fix(S)` is a subcomplex: if `S` fixes an interior
point of a simplex, it stabilizes the simplex and so fixes it pointwise.
It is closed and convex (fixed sets of isometries of a uniquely geodesic
space are convex).

## Step 1: `Z = Fix(ρ(N))` is nonempty and contractible

- Pick a vertex `x`. `G_x` is open and `K` compact, so `K/(K ∩ G_x)` is
  finite and `K·x` is finite, hence bounded.
- `X'` is complete CAT(0) (Bridson), so the circumcentre of `K·x` is fixed by
  `K`. So `Fix(K) ≠ ∅`, and `Fix(ρ(N)) ⊇ Fix(K)` because `ρ(N) ⊆ K`.
- `Z` is a nonempty closed convex subcomplex of dimension `≤ d`. The geodesic
  homotopy to a base point contracts it. Since `X'` is locally finite, the
  metric and CW topologies agree on `Z`, so `Z` is a contractible CW complex.

## Step 2: `P` acts on `Z` with finite stabilizers

- **Action.** For `f ∈ F`, `ρ(f)Z = Fix(ρ(fNf^{-1})) = Z` as `N ⊴ F`. `N`
  acts trivially. So `P` acts on `Z` by simplicial isometries, without
  inversions (Step 0).
- **Vertex stabilizers are finite.** Let `z` be a vertex of `Z`. Then
  `Stab_P(z) = Stab_F(z)/N`, where `Stab_F(z) = F ∩ ρ^{-1}(G_z) ⊇ N`. Define
  `Stab_F(z)/N -> G_z/(G_z ∩ K)` by `gN ↦ ρ(g)(G_z ∩ K)`.
  - Well defined: `ρ(N) ⊆ K ∩ G_z` because `N` fixes `z`.
  - Injective: if `ρ(g)^{-1}ρ(g') ∈ K` then `g^{-1}g' ∈ F ∩ ρ^{-1}(K) = N`.
  - `G_z` is compact and `G_z ∩ K` is open in it, so the target is finite.
- **Simplex stabilizers** lie in vertex stabilizers (Step 0), so are finite.

## Step 3: rational cohomological dimension

- The augmented cellular chain complex
  `0 -> C_{≤d}(Z; Q) -> ... -> C_0(Z; Q) -> Q -> 0` is exact (Step 1).
- Each `C_k(Z; Q) = ⊕_{σ} Q[P/P_σ]`, the sum over representatives of the
  `P`-orbits of `k`-simplices. Orientations are preserved because `P_σ` fixes
  `σ` pointwise.
- `P_σ` is finite, so `Q[P/P_σ] ≅ QP·e_σ` with `e_σ = |P_σ|^{-1} Σ_{h ∈ P_σ} h`
  an idempotent. It is a direct summand of `QP`, hence projective.
- This is a projective resolution of `Q` over `QP` of length `≤ d`, so
  `cd_Q P ≤ d` (Brown VIII.2).
- **Torsion-free subgroups.** If `P' ≤ P` is torsion-free, its stabilizers are
  trivial, and without inversions it acts freely on the contractible complex
  `Z`. Then `Z/P'` is a `K(P', 1)` of dimension `≤ d`, so `cd P' ≤ d`. In
  particular `Z^n ≤ P` forces `n ≤ d`, and `P` contains no `Z^∞`.
- **Finite subgroups.** A finite `Q ≤ P` has bounded orbits in the complete
  CAT(0) space `Z` (closed convex in `X'`), so it fixes the circumcentre. By
  Step 0 it then fixes the vertices of the simplex containing that point.
- **`d = 1`.** `Z` is a tree with a `P`-action with finite stabilizers. Step 5
  of `commensurated-witnesses-browder-survives-linear-kill-proof` then gives
  `P` finite or virtually free (`P` is finitely generated). ∎

## Step 4: the covered witnesses

- **Vertex stabilizers.** If `Λ` acts on `X` and `Σ = Stab_Λ(v)`, let
  `G = Aut(X)` with the topology of pointwise convergence on cells. By local
  finiteness, cell stabilizers are compact open (profinite). Put `K = G_v` and
  `ρ` the action of `F`. Then `F ∩ ρ^{-1}(K) = F ∩ Σ = N`.
  Commensuration is automatic: `[Σ : Σ ∩ λΣλ^{-1}] ≤ [G_v : G_v ∩ G_{λv}] <
  ∞`. For a developable complex of groups over a finite complex with
  finite-index local maps, the development is locally finite with finitely
  many shapes; when it is CAT(0) (e.g. Gromov's link condition), the local
  groups are such `Σ`.
- **Linear over any local field.** For `G` closed in `∏_j GL_{d_j}(k_j)`, let
  it act on `X = ∏_j B^{ext}_j`, where `B^{ext}_j = B(PGL_{d_j}(k_j)) × R` and
  `g` acts on the line factor by translation by `v_j(det g)/d_j`. With vertices
  of the line at `d_j^{-1}Z` this is a cellular action on a locally finite
  CAT(0) Euclidean polyhedral complex with finitely many shapes. A vertex is
  a pair `([L], s)`; if `g` fixes it then `gL = ϖ^m L` and
  `v(det g) = d_j m = 0`, so the stabilizer is `GL(L) ≅ GL_{d_j}(O_j)`,
  compact open. A cell stabilizer contains the finite intersection of the
  stabilizers of its vertices with finite index, so it is compact open too;
  in the closed subgroup `G` these stay compact open. The characteristic of
  `k_j` plays no role. (`dim X = Σ_j d_j`.)
- **Schlichting form.** In the cited proof, Step 6, `F̂` has the compact open
  normal subgroup `M = F̂ ∩ K` with `F̃ ∩ M = Ñ`. If `F̂` acts continuously on
  `X` with compact open stabilizers, take `G = F̂`, `K = M` and `ρ : F -> F̃`;
  the preimage of `M` is `N`. Conversely, if `P` acts on `X` properly (finite
  stabilizers), then `F̂ -> F̂/M ≅ P` makes `F̂` act with stabilizers the
  preimages of finite groups, which are compact open.
- **Right-angled buildings and cube complexes.** A locally finite right-angled
  building (finite thickness, finite Coxeter diagram) with its Davis
  realization, and a locally finite finite-dimensional CAT(0) cube complex,
  are locally finite CAT(0) polyhedral complexes with finitely many shapes;
  their automorphism groups have compact open cell stabilizers.

## Step 5: consequences and sharpness

- `U` contains every finitely presented group, in particular `Z^n` for all
  `n`. Thompson's `F` contains `F × F`, hence `Z^n` for all `n`, and
  `F ≤ T ≤ V`. `Z ≀ Z` contains `Z^∞`. By Step 3 none of these is `P`.
- **Lamplighter.** `L = F_2[t^{±1}] ⋊ ⟨t⟩` embeds diagonally in
  `B = Aff(F_2((t))) × Aff(F_2((t^{-1})))` by `(f, t^n) ↦ (x ↦ t^n x + f)` in
  each factor. It is discrete: an element near `1` has `|t^n| = 1`, so `n = 0`,
  and a Laurent polynomial with `v_t(f) ≥ 1` and `v_{t^{-1}}(f) ≥ 1` is `0`.
  `B` is closed in `PGL_2 × PGL_2` and acts on `T_3 × T_3` with compact
  stabilizers, so `L` acts properly on `T_3 × T_3` while containing `(Z/2)^r`
  for every `r`.
- **`SL_3(F_q[t])`.** It is finitely generated (`n ≥ 3`), discrete in
  `SL_3(F_q((t^{-1})))` since `F_q[t]` is discrete in `F_q((t^{-1}))`, and
  contains `{E_{12}(f) : f ∈ F_q[t]} ≅ (F_q[t], +)`, an infinite elementary
  abelian `p`-group. It acts properly on the Ã_2 building of
  `SL_3(F_q((t^{-1})))`.
- So in characteristic `p`, and on products of trees, finite-subgroup ranks of
  groups acting properly are unbounded: the rank invariant of the
  characteristic-0 kill cannot be extended, and `cd_Q` is what survives. The
  tree case `d = 1` is the only dimension where the geometry bounds ranks.

## What is not claimed

- Nothing about witnesses whose completions have no proper action on a
  finite-dimensional locally finite CAT(0) complex, such as Neretin-type
  almost-automorphism groups or groups acting only on infinite-dimensional
  cube complexes.
- No construction of a type `F` witness for `Z/2 ≀ Z` or Grigorchuk's group.
- The root is untouched; this is a class kill for `N_U`.
