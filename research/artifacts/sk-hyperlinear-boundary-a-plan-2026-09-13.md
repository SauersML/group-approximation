# sk-hyperlinear-boundary-a: plan (2026-09-13)

**Target.** Is `S_∂ = EL_N(LC(∂F_d, F_q) ⋊ F_d)/Z` hyperlinear? The open node is
`boundary-action-simple-kazhdan-group-is-hyperlinear`. My starting point (a) is unitary models built from the boundary action.

**Why it matters.** `S_∂` is infinite, simple, Kazhdan and nonsofic (reviewed PASS on main). A yes gives the first
hyperlinear nonsofic group, Pestov Question 3.4. A no gives an explicit non-hyperlinear group. Both outcomes are famous.

**Plan.**
1. **Close the reduction from the other side.** Main's Attempts already put `EL_N(L_k(1,2))` inside `S_∂` for `d = 2`.
   I aim for `LC(∂F_d, k) ⋊ F_d ≅ L_k(E_d)`, the Leavitt path algebra of the 2d-vertex graph of reduced letter pairs,
   via an explicit Cuntz–Krieger family. Brownlowe–Sørensen Theorem 4.1 (imported on main) then embeds it unitally in
   `L_k(1,2)`, so `S_∂ ≤ EL_N(L_k(1,2))`. For `d = 2`: `S_∂` is hyperlinear iff `EL_N(L_k(1,2))` is. The boundary
   moonshot then merges with `binary-leavitt-unit-group-hyperlinear` and is not a separate candidate.
2. **Firewall for start (a).** For a Kazhdan group, finite-rank compressions of any unitary representation with no
   finite-dimensional subrepresentation stay uniformly far from Hilbert–Schmidt almost-representations. So the regular,
   quasi-regular and boundary representations never compress to HS models of `S_∂`, or of any infinite simple
   Kazhdan group. Before authoring, check main's `kazhdan-*compression*` nodes for an existing statement.
3. **Only if a non-permutation, non-spatial mechanism appears:** test models that compose rank-metric almost-models over
   `F_2` with non-permutation representations of finite `GL_m(F_2)`.

**Not duplicating.** sk-hyperlinear-boundary-b (the von Neumann side) and the binary Leavitt campaign (`nh-*`,
`atlas-*`). I read their Attempts before adding anything.
