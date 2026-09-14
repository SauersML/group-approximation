# sk-hyperlinear-boundary-a: S_∂ hyperlinearity is the binary Leavitt question; compression models are dead (2026-09-13)

Lane sk-hyperlinear-boundary-a, start (a): unitary models from the boundary action. Everything here is unreviewed.
The complete proofs are in the route bodies named below. This artifact records what was checked and what it means.

## 1. The boundary crossed product is a Leavitt path algebra
Node: `boundary-crossed-product-is-a-leavitt-path-algebra`, with its `-proof` route.

`R_∂ = LC(∂F_d, k) ⋊ F_d ≅ L_k(E_d)`, where `E_d` is the reduced-letter graph: `2d` vertices, and an edge `a -> b` iff
`b != a^(-1)`. The map is vertex `a ↦ P_(C(a))` and edge `e_(ab) ↦ P_(C(ab)) u_a`.

Checks, each done by hand:
- **Cuntz–Krieger relations.** They follow from `g C(w) = C(gw)` for reduced `gw` and `C(a) = ⊔_(b != a^(-1)) C(ab)`.
  - `S_(ab)^* S_(a'b') = u_(a^(-1)) P_(C(ab)∩C(a'b')) u_(a')`, which is 0 unless `(a,b) = (a',b')`, when it is `P_(C(b))`.
  - `sum_b S_(ab)S_(ab)^* = P_(C(a))`.
- **Injectivity by simplicity.** `E_d` is finite and strongly connected (`a -> c -> a^(-1)` with `c ∉ {a, a^(-1)}`),
  every vertex emits `2d-1` edges, and every cycle has an exit. Main's Abrams–Aranda Pino import then makes
  `L_k(E_d)` simple.
- **Surjectivity.** `u_a = sum_(b != a^(-1)) P_(C(ab)) u_a + sum_(b != a) P_(C(b)) u_a`. The second sum is the image
  of the ghost edges `e_(a^(-1) b)^*`. Cylinder indicators are conjugates `u_g P_(C(a)) u_(g^(-1))`.
- **Model test.** For `d = 1`, i.e. `Z` acting on two points, the graph is two loops with no exits, and simplicity
  fails. That matches, because the crossed product is then not simple.

## 2. Equivalence with the binary Leavitt question
Nodes:
- `boundary-crossed-product-embeds-unitally-in-binary-leavitt`, via Brownlowe–Sørensen Thm 4.1 (unital when `E^0` is
  finite), already imported on main;
- `boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el`, with its `-proof` route.

Statement: for finite `k` of characteristic `p`, every `d >= 2` and `N >= 3`, `S_∂(d,k)` is hyperlinear iff
`EL_3(L_(F_p)(1,2))` is. Also, a hyperlinear `L_(F_p)(1,2)^x` makes every `S_∂(d,k)` hyperlinear.

What was checked:
- **Rank independence.** `E_M(M_n(S)) = E_(Mn)(S)` for `M >= 2`. Within a block, a transvection is a commutator
  through another block. With `M_2(L) ≅ L`, all `EL_M(L_p)` embed in one another.
- **Downward.** `k ⊗_(F_p) L_p ↪ M_m(L_p)` through the regular representation of `k`. The finite centre goes away
  because hyperlinearity passes to quotients by finite normal subgroups: `q = |F|^(-1) sum λ_f` is central with
  trace `1/|F|`, `L(G/F) ≅ qL(G)`, and corners of `R^ω` by projections of positive trace are ultraproducts of matrix
  algebras. Main's `mf-hyperlinear-of-finite-normal-quotient` is the converse direction, which needs MF, so this
  step is proved in the route and not cited.
- **Upward.**
  - The corner copy `EL_N(R) ↪ S_∂` is re-derived in the route; the same step appears in main's nonsoficity route.
  - The binary family inside `f R f`, `f = sum_(i<d) s_i t_i`, comes from the prefix code of `2d-2` words.
  - Every word `w` satisfies `f w = w` and `w^* f = w^*`, and the adjoint words are orthonormal.
  - For `d = 2` the first group of words is empty; the words are `s_1 s_1` and `s_1 s_2`, and `f = s_1 t_1`.

What it means:
- **One question, not two.** The boundary simple Kazhdan groups add no new hyperlinear-nonsofic candidate. Their
  question is `binary-leavitt-unit-group-hyperlinear` in its elementary form, and all of that campaign's Attempts
  and reductions (heat rounding, 24k feasibility, the Thompson V requirement) apply to `S_∂`.
- **The boundary structure gives extra tools.** The Leavitt attacks can also use the Kazhdan property of `S_∂`, its
  simplicity, and its explicit free-group boundary dynamics.
- **Thompson V.** Main records that any positive answer for Leavitt unit groups requires `thompson-v-hyperlinear`.
  By (ii) of the claim this now applies to `S_∂` in its EL form, but only through `EL_3(L_p)`. Whether `V` embeds in
  `EL_3(L_p)` was not checked. `L_p^x` contains `V`, and `diag(a,1,1)` puts `[L_p^x, L_p^x]` inside `EL_3`.

## 3. Firewall for start (a): no compression models
Node: `kazhdan-representations-have-no-hs-compression-models`, with its `-proof` route. It requires main's
`kazhdan-almost-invariant-corner-near-invariant-projection`.

Statement: if `pi` has no nonzero finite-dimensional subrepresentation, then every finite-rank compression has
normalized HS defect at least `epsilon_0 = min(1/968, kappa^2/242)` on some relation `s s^(-1) = 1`.

Proof sketch: a small defect gives `Tr(P - C(s)C(s)^*) <= epsilon d`, so `||[pi(s),P]||_HS^2 <= 2 epsilon d`. The
corner lemma then produces a nonzero invariant finite-rank projection, which is impossible.

This kills the naive form of start (a): spectral compressions of
- the regular representation,
- `ℓ^2(S_∂/H)`,
- the boundary orbit permutation modules,
- the induced representations from the action on `(F_q^N)^((F_d ξ))`.

Together with nonsoficity, any HS model of `S_∂` must be neither permutational nor spatial. Scope: this is folklore
in spirit, with a bounded check (main's Kazhdan compression nodes only). It is not claimed as a literature first.

## 4. Where start (a) stands
- The boundary action gives no route to hyperlinearity that the Leavitt campaign lacks. Any model must be genuinely
  finite and non-permutational.
- The only non-spatial finite candidates visible from here compose rank-metric almost-models over `F_p` with
  non-permutation representations of `GL_m(F_p)`. They need approximately multiplicative rank models of `R_∂`, but
  `R_∂` is purely infinite and has no Sylvester rank function, so that composition is also blocked unless the models
  are far from multiplicative on idempotents.
- No positive route is proposed. The open question stays open.

## 5. Manuscript
No change to `simple_kazhdan_sofic_group.tex`. `S_∂` is not in the note.
