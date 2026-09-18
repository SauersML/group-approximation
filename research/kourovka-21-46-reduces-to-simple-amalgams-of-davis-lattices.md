---
rg: 2
id: kourovka-21-46-reduces-to-simple-amalgams-of-davis-lattices
kind: claim
title: Torsion-free lattices in Aut(T) × Aut(X_{O_d}) with edge-transitive tree action are amalgams W_1 *_A W_2 of torsion-free Davis-complex lattices; a simple such amalgam is a finitely presented simple group of cohomological dimension 3, and non-residual finiteness can be imported from a free amalgam on one hyperplane
requires:
  - commensurated-subgroups-of-virtually-simple-groups-are-rf
---

**ESTABLISHED** (lane proof, not reviewed). This is a reduction, not an answer: it recasts
Amir–Lazarovich's second question (arXiv:2605.09493 l.2403, a torsion-free `Λ'^+`) as a Neumann-type
problem for Davis complexes, and isolates one extension gate (EXT). The cited theorems are:
- AL's local-to-global Theorem (l.113) and simplicity of `U^+` (AL Prop. l.897);
- the Bader–Shalom normal subgroup theorem, in Radu's form (arXiv:1712.01091 l.2128);
- Woodhouse's Leighton theorem for `X_{O_d}`, as cited by AL (l.2479).

## Setting

- `d >= 6`, `L = O_d`, `X = X_L`, a 2-dimensional CAT(0) square complex (`O_d` has no triangles).
- `U = U(Alt_{2d-1}) ≤ Aut(X)` is AL's universal group; `U^+` is simple of index 2.
- A **Davis lattice** is a torsion-free uniform lattice `W ≤ Aut(X)`. It acts freely on `X`: a cell
  stabilizer is finite, since vertex stabilizers are finite.
- Hyperplanes of `X` are `d`-regular trees; `W_L` is the right-angled Coxeter group of `L`.

## Statement

1. **Structure.** Let `T` be a locally finite tree and `Λ ≤ Aut(T) × Aut(X)` a torsion-free uniform lattice.
   - `Λ` is the fundamental group of a finite graph of Davis lattices: the vertex groups are the
     stabilizers `Λ_v` of vertices of `T`, embedded in `Aut(X)` by `pr_X`, and the edge groups have
     finite index in them. Inversions of `T` are handled by subdividing.
   - By Woodhouse–Leighton, every vertex group is commensurable up to conjugacy with `W_L`. So vertex
     groups are linear and residually finite, as the required node demands of commensurated subgroups.
   - If `Λ` acts edge-transitively on `T`, then `Λ ≅ W_1 *_A W_2` with `W_1, W_2` Davis lattices and
     `A = W_1 ∩ W_2` of finite index `c_1, c_2` in them.
   - If `Λ` inverts an edge, then `c_2 = 2` and `T` is the `c_1`-regular tree once its midpoints are
     forgotten.
2. **Converse, and cohomological dimension.** Let `W_1, W_2 ≤ Aut(X)` be Davis lattices with
   `A = W_1 ∩ W_2` of finite index in both, and set `Λ := W_1 *_A W_2`.
   - `Λ` acts on `T × X`, where `T` is its Bass–Serre tree, biregular of degrees `(c_1, c_2)`. The
     action on `X` is through the natural map `Λ → ⟨W_1, W_2⟩ ≤ Aut(X)`.
   - This action is free, proper and cocompact: vertex stabilizers of `T` are conjugates of `W_i`, which
     act freely and cocompactly on `X`.
   - So `Λ` is torsion-free and finitely presented, and every finite-index subgroup has cd exactly 3.
   - **Simple case.** If `Λ` (or `Λ^(∞)`, when of finite index) is simple, it answers Kourovka 21.46
     positively. Then `Λ → Aut(X)` is injective (its kernel meets `W_1` trivially), so `Λ ≅ ⟨W_1, W_2⟩`.
   - **The analogy.** This is the Davis-complex analogue of P. Neumann's 1973 question whether
     `F_m *_{F_k} F_n` can be simple, which Burger–Mozes answered using lattices in products of trees.
3. **Hyperplane sub-amalgams.** Let `H_0 ⊂ X` be a hyperplane, and put `F_i := Stab_{W_i}(H_0)`.
   - Each `F_i` acts faithfully, freely and cocompactly on the tree `H_0`, so it is free.
   - `⟨F_1, F_2⟩ ≤ Λ` is canonically `F_1 *_{F_1 ∩ F_2} F_2`, a torsion-free uniform lattice in
     `Aut(T') × Aut(H_0)`, where `T' ⊆ T` is its own Bass–Serre tree.
   - If this free amalgam is not residually finite for one `H_0`, then `Λ` is not residually finite.
4. **Reduction.** Let `W_1, W_2 ≤ U` be Davis lattices with `A = W_1 ∩ W_2` of finite index, and assume:
   - **(N1)** `⟨W_1, W_2⟩` is vertex-transitive on `X` and non-discrete, and at some vertex `v` its
     stabilizer acts on `B_1(v)` as `U_v` does;
   - **(N2)** the closure of `pr_T(Λ)` acts 2-transitively on `∂T`. For example, `pr_T(Λ)` is
     non-discrete and the local actions `W_i ↷ W_i/A` contain `Alt(c_i)`, `c_i >= 6`, by Burger–Mozes
     Props. 3.3.1–3.3.2 as Radu uses them; we have not checked the biregular case;
   - **(N3)** `Λ` is not residually finite, for instance by item 3.

   Then `Λ^(∞)` is a torsion-free, finitely presented, infinite simple group of cohomological dimension 3.

   Conversely, every positive answer of this normal-subgroup-theorem type in `T × X_{O_d}` whose tree
   closure is boundary-2-transitive arises this way. A locally 2-transitive closure `H_T` has `(H_T)_v` equal
   to the closure of `pr_T(Λ_v)`, so `Λ_v` is transitive on the link of `v` and `Λ` is edge-transitive.
   Apply item 1 to the simple part.
5. **AL as the instance with torsion.** AL's lattice acts on `T_c` edge-transitively, with vertex group
   `W_L` and an inverting involution `z`. So it is `W_L *_A (A ⋊ ⟨z⟩)`, with `A` the edge stabilizer. Its
   torsion is the involutions of `W_L` and of `A ⋊ ⟨z⟩`. The square diagonals `DD'` survive into the simple
   part (`amir-lazarovich-simple-lattice-has-torsion-iff-index-four`). The question is whether both
   factors can be replaced by Davis lattices.
6. **Constraints on a torsion-free solution.**
   - (a) **Commensurability rigidity.** Suppose a group `Λ'` has a finite-index simple subgroup `Λ` that
     contains torsion. Then every group abstractly commensurable with `Λ'` has torsion, since each
     finite-index subgroup of `Λ'` contains `Λ`. This applies to every AL lattice with `Λ = Λ'^+`
     (AL's explicit scaffolding, `amir-lazarovich-simple-lattices-have-torsion`). So a torsion-free
     answer must come from a new commensurability class; no subgroup or finite cover of a known AL
     lattice works.
   - (b) **Vertex-transitive Davis lattices.** A torsion-free, vertex-transitive `W` acts simply
     transitively, and `W\X` is a one-vertex square complex whose link is `O_d`. So `|V(O_d)|` is even
     and `4 | |E(O_d)|`, because each square contributes 4 corners at the unique vertex.
     - With `|V| = C(2d-1, d-1)` and `|E| = d|V|/2`, this means `s_2(d) >= 2` and `v_2(d) + s_2(d) >= 4`,
       where `s_2` is the binary digit sum. Indeed `v_2(C(2d,d)) = s_2(d)` by Kummer.
     - The admissible `d >= 6` are `12, 14, 15, 20, 22, 23, 24, 26, …`; none of `6, …, 11` qualifies.
     - Such `W` is never type-preserving: a type-preserving automorphism sending a vertex to a
       neighbour inverts that edge.
     - So if (N1) is to come from `W_1` alone, `d >= 12` and a one-vertex square complex with link `O_d`
       are needed. Its existence is OPEN.
     - The commutator-square design (squares `s t s^{-1} t^{-1}`) needs twin vertices in `O_d` and fails.
       (N1) can also hold for the pair without either `W_i` being vertex-transitive.
   - (c) **Where non-residual finiteness can live.** By the required node, the vertex groups `W_i` must be
     residually finite, and they are. Non-residual finiteness has to come from non-commensurated
     subgroups, such as the hyperplane sub-amalgams of item 3.
7. **The gate (EXT): extend a free amalgam from a hyperplane.** Find:
   - a torsion-free, edge-transitive, non-residually-finite lattice `F_a *_{F_e} F_b` in
     `Aut(T') × Aut(T_d)`, of Burger–Mozes, Rattaggi, Bondarenko–Kivva or Radu type; and
   - Davis lattices `W_1, W_2` having a common hyperplane `H_0 ≅ T_d` with `Stab_{W_1}(H_0) = F_a` and
     `Stab_{W_2}(H_0) = F_b`, such that `W_1 ∩ W_2` has finite index in both and
     `Stab_{W_1 ∩ W_2}(H_0) = F_e`.

   Then (N3) holds by item 3. **Finite form:** take `W_2 = g W_1 g^{-1}` with `g ∈ Comm_{Aut X}(W_1)`,
   `g H_0 = H_0` and `g|_{H_0} = h`, where `F_b = h F_a h^{-1}`. Then EXT asks for a *relative Leighton
   theorem for one hyperplane*:
   - a finite cover `Y'` of `Y = W_1\X` containing the hyperplane graph `Z' = (F_a ∩ h^{-1}F_a h)\H_0`;
   - a second covering map `Y' → Y` whose restriction to `Z'` is the covering induced by `h`.

   The first covering exists because `W_L` is hyperbolic and virtually special, so its hyperplane
   subgroups are virtual retracts (Haglund–Wise). The second was the open step.

   **Update (09-18): EXT is proved** by `hyperplane-extensions-into-davis-lattices-are-split`. The
   Coxeter retraction onto `W_{st(D)}` gives a homomorphic section from the carrier automorphisms to
   `Aut(X)`. The resulting `Λ` is split, `K_0 ⋊ Γ`, so it is never just-infinite. The open gate is
   therefore **(IRR)**: `A` must contain no nontrivial subgroup that is normal in both `W_i`.
   - AL solved the analogous extension for *involutive* BMW seeds through their interlacing pairs.
   - EXT asks the same for free, torsion-free seeds, with no simple-transitivity requirement.

## Proof

1. **Item 1.**
   - Bass–Serre theory for `Λ ↷ T`, subdivided so that there are no inversions, gives the graph of groups.
   - `pr_X` is injective on each `Λ_v`: its kernel is discrete and lies in the compact group `Aut(T)_v`,
     so it is finite, hence trivial.
   - `pr_X(Λ_v)` is discrete, because `Aut(T)_v` is compact. It is cocompact on `X`, because it is the
     stabilizer of the slice `{v} × X`.
   - Edge groups have finite index because `T` is locally finite. An edge-transitive action without
     inversions has one edge in the quotient graph, so `Λ = Λ_v *_{Λ_e} Λ_w`.
   - With inversions, the midpoint stabilizer is a Davis lattice containing `Λ_e` with index 2.
2. **Item 2.**
   - The natural map to `Aut(X)` is well defined because both inclusions agree on `A`.
   - **Freeness.** An element fixing a vertex `(t, x)` lies in a conjugate of some `W_i` and fixes `x`,
     so it is trivial. Properness and cocompactness follow from the finite quotient `Λ\T` and from
     cocompactness of the `W_i` on `X`.
   - **Finite presentation.** `W_i` are finitely presented and `A` has finite index, so `A` is finitely
     generated.
   - **cd = 3.** `Λ` acts freely and cocompactly on the contractible 3-complex `T × X`, so
     `cd Λ = 3` iff `H^3_c(T × X) ≠ 0`.
     - By Künneth, `H^3_c(T × X) ⊇ H^1_c(T) ⊗ H^2_c(X)`. Here `H^1_c(T)` is free abelian and nonzero,
       since `T` has infinitely many ends.
     - `H^2_c(X) ≅ H^2(W; ZW) ≠ 0`, because `vcd W_L = 2`: `L` is triangle-free and contains cycles.
     - This is AL's remark "torsion free uniform lattices in `T_c × X_{O_d}` have cd 3", made explicit.
   - **Injectivity when simple.** The kernel of `Λ → Aut(X)` is a normal subgroup meeting `W_1` trivially,
     so it is proper, hence trivial.
3. **Item 3.**
   - **Freeness of `F_i`.** Take `f ∈ F_i` fixing a vertex of `H_0`, i.e. the midpoint of an edge `e`
     dual to `H_0`. Either `f` fixes `e`, so it fixes a vertex and `f = 1`; or `f` flips `e`, so `f^2`
     fixes a vertex, `f^2 = 1`, and `W_i` has torsion. So `F_i` acts freely.
   - **Faithfulness and cocompactness.** The same argument gives faithfulness on `H_0`. Cocompactness
     holds because `W_i` has finitely many orbits of squares.
   - **The sub-amalgam.** `F_1 ∩ A = Stab_A(H_0) = F_2 ∩ A`. So by the normal form theorem, the subgroup
     generated by `F_1` and `F_2` in `W_1 *_A W_2` is `F_1 *_{F_1 ∩ F_2} F_2`.
   - **Inheritance.** Non-residual finiteness passes to overgroups.
4. **Item 4.**
   - **The X-closure.** By (N1) and AL's local-to-global theorem, `⟨W_1, W_2⟩` is dense in `U`.
     - `U` is just non-compact. A nontrivial closed normal `N ⊴ U` meets the simple group `U^+` either
       trivially or in `U^+`.
     - If trivially, `N` has order at most 2 and centralizes `U^+`, whose centralizer is trivial (the
       action on `∂W_L` is faithful, as AL use).
   - **The T-closure.** By (N2) and Radu's remark, `H_T` is just non-compact.
   - **Just-infinite.** Bader–Shalom makes `Λ` and all its finite-index subgroups just-infinite:
     closed finite-index subgroups of `U`, and of `H_T` by BM Prop. 3.1.2, keep the hypotheses.
   - **Simplicity.** By (N3), `Λ^(∞) ≠ 1`, so it has finite index. It is just-infinite with no proper
     finite-index subgroups, hence simple, exactly as in Radu's proof of the NST corollary.
   - **Properties.** It is torsion-free, finitely presented (finite index in `Λ`), and of cd 3 by item 2.
   - **Converse.** The statement about `(H_T)_v` is the standard fact that `pr_T(λ) ∈ Aut(T)_v` forces
     `λ ∈ Λ_v`.
5. **Item 6(b).** Covered in the statement: the corners of squares at a single vertex are exactly the
   edges of the link. On twins: `s t s^{-1} t^{-1}` produces the link edges
   `{s,t}, {s^{-1},t}, {s^{-1},t^{-1}}, {s,t^{-1}}`, so `N(s) = N(s^{-1})`. But distinct vertices of
   `O_d` have distinct neighbourhoods.

## What this changes for 21.46

- The Amir–Lazarovich route is no longer "find a torsion-free interlacing pair". It becomes: **find two
  commensurable Davis lattices whose amalgam is simple.**
- The sub-amalgam on a hyperplane is a Neumann/Burger–Mozes free amalgam. So the only non-local
  ingredient is EXT, a relative Leighton theorem for one hyperplane of `X_{O_d}`.
- (N1) and (N2) are local conditions of the kind AL and Radu verify.
- Two routes are closed by the required node:
  - three trees with an imported 2-dimensional witness;
  - any geometry with a Lie or algebraic factor.

## Lesson for general BH

- **Simple hosts are amalgams of lattices.** Hosts built from lattices in products with an
  edge-transitive tree factor *are* amalgams `W_1 *_A W_2` of lattices of the other factor. Simplicity is
  a property of how two commensurable lattices sit together inside a non-linear locally compact group.
- **The hardness lives on a hyperplane.** The hard part can be read on a single hyperplane, where it is a
  free amalgam. That is also where a non-residually-finite input enters.
- **Extension is the operation.** For BH-type constructions, the useful operation is therefore
  *extending commensurations from a hyperplane to the whole complex* (a relative Leighton theorem).
  Building a new lattice from scratch is not needed.
