# FP_n versus FH_n (Zaremsky Problem 1.4), part 1: definitions, free versus proper, low n

Lane z1-04-fp-fh, 2026-09-13. Root: `zaremsky-1-04-type-fpn-equals-type-fhn`.
Part 2 (`zp-fpn-fhn-2026-09-13-part2.md`) has the acyclic-kernel criterion,
the `n = 3` characterization and the obstruction analysis. Status of every
statement: unreviewed.

## 0. Conventions

- Coefficients are `ℤ`; modules are left `ℤG`-modules.
- `G` is of type `FP_n` if the trivial module `ℤ` has a projective
  resolution `P_*` with `P_i` finitely generated for `i ≤ n`. Equivalently
  there is an exact sequence `F_n → ⋯ → F_0 → ℤ → 0` of finitely generated
  free modules; given one, extend it by any free resolution of
  `ker(F_n → F_{n−1})`.
- A CW complex `X` is *`(n−1)`-acyclic* if `X ≠ ∅` and `H̃_i(X) = 0` for
  `0 ≤ i ≤ n−1`.
- A *`G`-CW complex* is a CW complex on which `G` acts by cellular
  homeomorphisms permuting the open cells. The action is *free* if no
  nontrivial element fixes a point, and *proper* if every cell has finite
  setwise stabilizer. It is *cocompact* iff there are finitely many
  `G`-orbits of cells, because a compact subset of a CW complex meets only
  finitely many open cells.
- `FH_n^prop`: some `(n−1)`-acyclic `G`-CW complex has a proper cocompact
  action. This is Zaremsky's printed reading. `FH_n^free`: the same with a
  free action, which is Bestvina–Brady's and Leary's convention.
- **Skeleton remark.** Suppose `X` is `(n−1)`-acyclic and has finitely many
  orbits of cells of dimension `≤ n`. Then the `n`-skeleton `X^{(n)}` is
  `(n−1)`-acyclic, since `H_i(X^{(n)}) → H_i(X)` is an isomorphism for
  `i ≤ n−1`, and `X^{(n)}` is cocompact. So cocompactness may be weakened to
  finitely many orbits of cells in dimensions `≤ n`.

## 1. Generalized Schanuel lemma, in the form used

**Lemma S.** Let `M` be of type `FP_k` (`k ≥ 1`). Let
`D_{k−1} → ⋯ → D_0 → M → 0` be exact with every `D_i` finitely generated
projective. Then `K := ker(D_{k−1} → D_{k−2})` is finitely generated. (For
`k = 1`, `K := ker(D_0 → M)`.)

*Proof.* Let `P_*` be a projective resolution of `M` with `P_i` finitely
generated for `i ≤ k`, and set `K' = ker(P_{k−1} → P_{k−2}) = im(P_k)`,
which is finitely generated. Schanuel's lemma applied to
`0 → K_0 → D_0 → M → 0` and `0 → K'_0 → P_0 → M → 0` gives
`K_0 ⊕ P_0 ≅ K'_0 ⊕ D_0`. Now apply it to
`0 → K_1 → D_1 ⊕ P_0 → K_0 ⊕ P_0 → 0` and
`0 → K'_1 → P_1 ⊕ D_0 → K'_0 ⊕ D_0 → 0`, and continue by induction. The
result is `K ⊕ (f.g. projective) ≅ K' ⊕ (f.g. projective)`, so `K` is a
direct summand of a finitely generated module. ∎

## 2. Theorem C: the proper and free readings coincide

**Theorem C.** If `G` acts properly and cocompactly on an `(n−1)`-acyclic CW
complex `X`, then `G` acts freely and cocompactly on an `(n−1)`-acyclic CW
complex `W`. The converse is trivial. So `FH_n^prop = FH_n^free`.

*Construction.* Let `J = J_n(G)` be the `(n+1)`-fold join of the discrete
set `G`: the simplicial complex on vertex set `G × {0,…,n}` whose simplices
are the vertex sets with at most one vertex in each layer `G × {i}`. `G` acts
by `g·(h,i) = (gh,i)`, and the action is free on `J`: a point
`Σ t_i (h_i,i)` is fixed by `g` only if `gh_i = h_i` for some `i`. For
`S ⊆ G` let `J(S)` be the full subcomplex on `S × {0,…,n}`. It is the join of
`n+1` copies of `S`, so it is finite when `S` is finite and
`(n−1)`-connected when `S ≠ ∅`.

For a cell `e` of `X`, let `K(e)` be the smallest subcomplex containing `e`;
it is finite. Choose representatives `e_1, …, e_m` of the orbits of cells
and put `C = K(e_1) ∪ ⋯ ∪ K(e_m)`, a finite subcomplex. Define
`S_e = { g ∈ G : K(e) ⊆ gC }`.

- *Nonempty.* If `e = g e_j` then `K(e) = gK(e_j) ⊆ gC`.
- *Finite.* `K(e) ⊆ gC` forces `g^{-1}e` to be one of the finitely many cells
  of `C`. For each such cell `c` in the orbit of `e`, the set
  `{ g : g c = e }` is a coset of the finite stabilizer of `c`.
- *Equivariant.* `S_{ge} = g S_e`.
- *Monotone.* If the open cell `e'` meets the closure of `e`, then `e'` lies
  in every subcomplex containing `e`. So `K(e') ⊆ K(e)` and
  `S_e ⊆ S_{e'}`.

Let `W ⊆ X × J` be the union over cells `e` of `e × J(S_e)`, with the weak
(CW) topology on the union of product cells `e × σ`.

- *Subcomplex.* By monotonicity, the closure of `e × J(S_e)` lies in
  `⋃_{e' ⊆ K(e)} e' × J(S_{e'})`.
- *Invariant and free.* `g(e × J(S_e)) = ge × J(S_{ge})`, and `G` acts freely
  on the second factor.
- *Cocompact.* A product cell `e × σ` with `σ ⊆ J(S_e)` can be translated so
  that `e` is one of `e_1, …, e_m`, and each `J(S_{e_j})` is finite.

*Homology.* Let `p : W → X` be the projection. Over an open cell `e` the
preimage is exactly `e × J(S_e)`: a point of `e` lies in `e'' × J(S_{e''})`
only for `e'' = e`. Filter `X` by skeleta `X_k` and `W` by `W_k = p^{-1}(X_k)`.
Excision and the characteristic maps give

`H_{k+q}(W_k, W_{k−1}) ≅ ⊕_{e ∈ X_k∖X_{k−1}} H_q(J(S_e))`,

and `p` induces the map to `H_{k+q}(X_k, X_{k−1}) ≅ ⊕_e H_q(pt)` given by
collapsing `J(S_e)` to a point. Since `J(S_e)` is `(n−1)`-connected, this is
an isomorphism for `q ≤ n−1`. So `p` maps the `E^1` pages of the two skeletal
spectral sequences isomorphically in the region `q ≤ n−1`.

Every entry of total degree `j ≤ n−1`, and every differential into or out of
such an entry, lies in that region: a differential out of `(k,q)` lands in
total degree `j−1`, and one into it starts in total degree `j+1` with a
smaller `q`. By induction on the page, the entries of total degree `≤ n−1`
agree, and both filtrations are finite because the complexes are
finite-dimensional. Hence `H_j(W) ≅ H_j(X)` for `j ≤ n−1`, and `W` is
`(n−1)`-acyclic. ∎

## 3. Theorem A: FH_n implies FP_n

**Theorem A.** If `G` is of type `FH_n^prop`, then `G` is of type `FP_n`.

*Proof.* By Theorem C and the skeleton remark there is a free `G`-CW complex
`W` that is `(n−1)`-acyclic and has finitely many orbits of cells in
dimensions `≤ n`. Its cellular chain complex gives an exact sequence
`C_n(W) → ⋯ → C_0(W) → ℤ → 0`. Exactness at `C_{n−1}, …, C_0` and at `ℤ` is
`(n−1)`-acyclicity, and each `C_i(W)` is free on one generator per orbit of
`i`-cells, hence finitely generated. ∎

(Alternatively, Brown's criterion: permutation modules `ℤG ⊗_{ℤF} ℤ_χ` with
`F` finite are of type `FP_∞`. The free replacement avoids that citation.)

## 4. Theorem B: FP_n implies FH_n for n ≤ 2

**Theorem B.** For `n ≤ 2`, every group of type `FP_n` is of type `FH_n^free`.

*Proof.*
- `n = 0`: `G` acts freely and cocompactly on the discrete set `G`.
- `n = 1`: `FP_1` means the augmentation ideal `I_G` is finitely generated.
  If generators are written using finitely many group elements generating
  `H ≤ G`, then `I_G = ℤG · I_H`, and applying `ℤ ⊗_{ℤG}` shows
  `ℤ[G/H]` has augmentation kernel zero, so `H = G`. The Cayley graph for
  that finite generating set is connected, with one orbit of vertices and
  finitely many orbits of edges.
- `n = 2`: let `Γ` be the Cayley graph for a finite generating set. The
  sequence `C_1(Γ) → C_0(Γ) → ℤ → 0` is exact with finitely generated free
  terms, so by Lemma S (`k = 2`) `Z_1 = ker(C_1 → C_0) = H_1(Γ)` is finitely
  generated. Since `Γ` is connected, the Hurewicz map `π_1(Γ,1) → H_1(Γ)` is
  onto. Choose closed edge loops `γ_1, …, γ_k` at the vertex `1` whose classes
  generate `H_1(Γ)` as a `ℤG`-module. Attach 2-cells `D_{g,i}` along `gγ_i`
  for `g ∈ G` and `i ≤ k`. The result `X` is a free `G`-CW complex with one
  orbit of vertices, finitely many orbits of edges and `k` orbits of
  2-cells. It is connected and `H_1(X) = H_1(Γ)/ℤG⟨[γ_i]⟩ = 0`. ∎
