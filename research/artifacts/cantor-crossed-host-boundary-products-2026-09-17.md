# Boundary products of Cantor crossed product hosts, and hard minimal Z^2 SFTs

Lane c-cantor, swarm-0917, 2026-09-17. Target hole:
`decidable-group-algebras-have-fp-cantor-crossed-hosts`.

## 0. Results and nodes

- **Theorem P (product closure).** Take a valid host `(P, X)` and tensor it with the boundary
  crossed product of a free group. The result is again a valid host, over `P × F_d` and
  `X × ∂F_d`. The new host is not directly finite, so it has no unital rank model.
  - Node: `cantor-crossed-hosts-are-closed-under-boundary-products` (ESTABLISHED), route
    `cantor-crossed-hosts-are-closed-under-boundary-products-proof`.
- **Theorem H (hard minimal SFTs).** For every recursive time bound `T` there is a minimal
  `Z^2`-SFT whose square-pattern language is not decidable within `T`, up to constants.
  - Node: `minimal-z2-sfts-have-no-uniform-language-time-bound` (ESTABLISHED), route
    `minimal-z2-sfts-have-no-uniform-language-time-bound-proof`.
- **Reduction R1.** The target follows from one open existence statement about free minimal
  quantum rigid `Z^2`-SFTs and embeddings into their boundary products.
  - Nodes: `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` (OPEN),
    route `cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts`.
- **Reduction R2 (group level).** Boone–Higman follows from embedding the group, not its group
  algebra, into the units of the Leavitt tensor of some valid host.
  - Nodes: `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units` (OPEN), route
    `boone-higman-via-units-of-cantor-crossed-leavitt-tensors`.

Throughout, `k` is a field, `LC(X, k)` is the algebra of locally constant functions, and
`LC(X, k) ⋊ P` has product `(f g)(f' h) = f (f' ∘ g^−1) gh`, as in
`fjc-crossed-product-leavitt-hosts-2026-09-16`.

A **valid host over `k`** is a pair `(P, X)` with the following properties:
- `P` is torsion-free and satisfies FJCw (Section 2);
- `X` is a nonempty compact totally disconnected Hausdorff `P`-space;
- `B = LC(X, k) ⋊ P` is finitely presented, simple, and has centre `k`.

FJCw implies the Farrell–Jones hypothesis of the target, so a valid host satisfies every
condition of the target except the embedding of `F_2[G]`.

## 1. Theorem P

Let `(P, X)` be a valid host over `k` with algebra `B`. Fix `d >= 2` and let
`L_∂ = LC(∂F_d, k) ⋊ F_d`. Put `Q = P × F_d` and `Y = X × ∂F_d`, with the product action. Then:

1. `LC(Y, k) ⋊ Q ≅ B ⊗_k L_∂` as unital `k`-algebras.
2. `(Q, Y)` is a valid host over `k`.
3. `B ⊗ L_∂` contains a unital copy of `L_k(1, d)`. So it is not directly finite, and it has no
   unital homomorphism into any rank ultraproduct `prod_ω M_(n)(F) / {rank-null}`.
4. `B ⊗ L_∂` contains `B ⊗ 1` unitally. So every group algebra that embeds unitally in `B` also
   embeds unitally in the new host.

### 1.1 The tensor isomorphism

- **Functions.** Let `X` and `W` be compact totally disconnected Hausdorff spaces; here `W = ∂F_d`.
  The clopen rectangles `U × V` form a basis of `X × W`, which is compact. So every locally
  constant `f` on `X × W` is constant on the cells of a finite partition into clopen rectangles.
  Hence `m : LC(X, k) ⊗ LC(W, k) -> LC(X × W, k)`, `f ⊗ f' |-> ((x, w) |-> f(x) f'(w))`, is onto.
  - It is injective: choose partitions `{U_i}` and `{V_j}` refining the supports of a finite
    tensor. Then `{1_(U_i) ⊗ 1_(V_j)}` is linearly independent, and it maps to the linearly
    independent family of indicators of the disjoint nonempty rectangles `U_i × V_j`.
  - `m` is multiplicative, so it is an algebra isomorphism.
- **Crossed products.** As vector spaces,
  `LC(Y, k) ⋊ Q = ⊕_((g,h) ∈ Q) LC(Y, k)(g, h)` and
  `B ⊗ L_∂ = ⊕_(g, h) (LC(X, k) ⊗ LC(∂F_d, k)) (g ⊗ h)`.
  - Map `(f ⊗ f')(g, h) |-> f g ⊗ f' h`, using `m` on coefficients. This is a linear bijection.
  - It is multiplicative, because the action is coordinatewise:
    `(f ⊗ f') ∘ (g, h)^−1 = (f ∘ g^−1) ⊗ (f' ∘ h^−1)`. Therefore
    `((f ⊗ f')(g,h))((e ⊗ e')(g',h')) = (f (e ∘ g^−1) ⊗ f' (e' ∘ h^−1))(gg', hh')`, and this
    equals `(f g)(e g') ⊗ (f' h)(e' h')` computed in `B ⊗ L_∂`.
  - Units go to units. ∎(1)

### 1.2 Finite presentation

- `L_∂ ≅ L_k(E_d)` by `boundary-crossed-product-is-a-leavitt-path-algebra`.
  - The Leavitt path algebra of a finite graph is presented by the finitely many vertex, edge
    and ghost-edge generators and the finitely many Cuntz–Krieger relations.
  - So `L_∂` is finitely presented.
- If `A = k<S | R>` and `C = k<T | U>` with `S, T, R, U` finite, then
  `A ⊗ C = k<S ⊔ T | R ∪ U ∪ {st − ts : s ∈ S, t ∈ T}>`.
  - The right-hand side `D` maps onto `A ⊗ C`.
  - Conversely, `A -> D` and `C -> D` are well defined and have commuting images. So they induce
    `A ⊗ C -> D`, which is inverse on generators.
- So `B ⊗ L_∂` is finitely presented.

### 1.3 Simplicity

**Lemma.** If `A` is a simple unital `k`-algebra with `Z(A) = k` and `C` is a simple unital
`k`-algebra, then `A ⊗ C` is simple. No finiteness is needed.

*Proof.*
1. Let `I` be a nonzero ideal. Pick `x ∈ I \ 0` of minimal tensor rank `n`,
   `x = Σ_(i<=n) a_i ⊗ c_i`. The `a_i` and the `c_i` are each linearly independent.
2. `A` is simple, so `Σ_j u_j a_1 v_j = 1` for some `u_j, v_j`. Put
   `x' = Σ_j (u_j ⊗ 1) x (v_j ⊗ 1) = Σ_i a_i' ⊗ c_i`, with `a_1' = 1`.
   - `x' ∈ I`, and `x' != 0` because the `c_i` are independent.
   - By minimality `x'` has rank `n`.
3. For `a ∈ A`, `(a ⊗ 1) x' − x' (a ⊗ 1) = Σ_(i>=2) [a, a_i'] ⊗ c_i` lies in `I` and has rank
   `< n`. So it is `0`, and each `[a, a_i'] = 0`.
   - Hence `a_i' ∈ Z(A) = k`.
   - Independence of `a_1' = 1, a_2', …, a_n'` inside `k` forces `n = 1`.
4. So `x' = 1 ⊗ c` with `c != 0`. `C` is simple, so `Σ_j w_j c z_j = 1`, and
   `Σ_j (1 ⊗ w_j) x' (1 ⊗ z_j) = 1 ∈ I`. ∎

Apply it with `A = B`, which is central simple by hypothesis, and `C = L_∂`.
- `L_∂` is simple by `boundary-crossed-product-is-a-leavitt-path-algebra`: its review re-derived
  the Abrams–Aranda Pino simplicity import.

### 1.4 Centre

**Lemma.** For unital `k`-algebras, `Z(A ⊗ C) = Z(A) ⊗ Z(C)`.

*Proof.* Let `z = Σ a_i ⊗ c_i` be central, with the `c_i` independent.
- Commuting with `a ⊗ 1` gives `Σ [a, a_i] ⊗ c_i = 0`, so every `a_i ∈ Z(A)`.
- Rewrite `z = Σ a_i ⊗ c_i` with the `a_i ∈ Z(A)` independent. Commuting with `1 ⊗ c` gives every
  `c_i ∈ Z(C)`.
- The reverse inclusion is clear. ∎

`Z(L_∂) = k` by Lemma 6.3 of `fjc-crossed-product-leavitt-hosts-2026-09-16`.
- The boundary action is minimal: every cylinder `C(w)` meets every orbit.
- It is topologically free, since each `g != e` fixes exactly the two endpoints of its axis.

So `Z(B ⊗ L_∂) = k ⊗ k = k`.

### 1.5 The group and the space

- **Torsion.** `Q = P × F_d` is torsion-free: if `(g, h)^m = e`, then `g^m = e` and `h^m = e`.
- **The space.** `Y` is nonempty, compact, Hausdorff and totally disconnected.
- **FJCw.** `P` satisfies FJCw by hypothesis. `F_d` acts properly and cocompactly by isometries on
  its Cayley tree, which is CAT(0), so `F_d` is a CAT(0)-group and satisfies FJCw (Wegner,
  quoted in Section 2). By Wegner's direct product inheritance, `Q` satisfies FJCw. ∎(2)

### 1.6 No rank model

- `boundary-crossed-product-carries-leavitt-family` gives `s_i, t_i ∈ L_∂` with `t_i s_j = δ_ij`
  and `Σ s_i t_i = 1`. Their images `1 ⊗ s_i` and `1 ⊗ t_i` satisfy the same relations.
- `t_1 s_1 = 1`, but `s_1 t_1 = 1 − Σ_(i>=2) s_i t_i != 1`. Indeed `s_2 t_2 != 0`, since
  `t_2 s_2 t_2 s_2 = 1`, and `b |-> 1 ⊗ b` is injective.
- A rank ultraproduct `M` is directly finite. For square matrices,
  `rk(I − AB) = rk(I − BA)`, so `rk(1 − ab) -> 0` implies `rk(1 − ba) -> 0`.
- Let `φ : B ⊗ L_∂ -> M` be unital.
  - `φ(t_1) φ(s_1) = 1`, so direct finiteness gives `φ(s_1 t_1) = 1`.
  - Then `Σ_(i>=2) φ(s_i t_i) = 0`. The `φ(s_i t_i)` are pairwise orthogonal idempotents, so
    multiplying by `φ(s_2 t_2)` gives `φ(s_2 t_2) = 0`.
  - Hence `1 = φ(t_2 s_2 t_2 s_2) = φ(t_2) φ(s_2 t_2) φ(s_2) = 0` in `M != 0`, a contradiction.
- So there is no unital homomorphism into `M` at all, injective or not. ∎(3)
- Part 4 is `b |-> b ⊗ 1`. ∎

### 1.7 What Theorem P changes

- **Attempts 2 and 3 of the target.** Their gate is: a valid host with amenable `P` has a faithful
  unital rank model. Restricting it to `F_2[G]^x` would force `G` to be `F_2`-linear sofic. That
  argument needs a unital rank model of the host. Hosts over `Z^2 × F_d` have none, by part 3.
  - So linear soficity of every decidable group is **not** a consequence of the target, as far as
    any argument in the graph goes.
  - It is a consequence only of the amenable-`P` case.
- **Attempt 6 (landed 2026-09-17).** A viable family must use a non-free, finitely presented `P`
  and SFTs whose ball languages have no uniform recursive time bound.
  - `Q = Z^2 × F_d` is non-free and finitely presented.
  - A ball pattern of `Ω × ∂F_d` is a pair of a `Z^2` ball pattern and an `F_d` ball pattern, so
    its language is exactly as hard as that of `Ω`.
  - Theorem H shows that minimal `Z^2`-SFTs of arbitrarily high language complexity exist.
  - So the complexity kill of Attempt 4 does not reach the family `Z^2 × F_d`.
  - What is missing is freeness and quantum rigidity for the hard SFTs (Section 3.4).

## 2. Imported: FJCw and its inheritance (Wegner, arXiv:1308.2432)

Source: C. Wegner, *The Farrell–Jones conjecture for virtually solvable groups*,
arXiv:1308.2432. Read from the e-print TeX source on 2026-09-17. Verbatim:

> **Definition ($K$-theoretic Farrell-Jones Conjecture).** We say that $G$ satisfies the
> *$K$-theoretic Farrell-Jones Conjecture with respect to the family $\mathcal{F}$* if the assembly
> map $H^G_m(E_{\mathcal{F}}G;\mathbf{K}_\mathcal{A}) \to H^G_m(\pt;\mathbf{K}_\mathcal{A}) \cong
> K_m(\int_G \mathcal{A})$ induced by the projection $E_\mathcal{F}G \to \pt$ is an isomorphism for
> all $m \in \Z$ and every additive $G$-category $\mathcal{A}$.

> **Definition (FJCw).** We say that a group $G$ satisfies the *Farrell-Jones Conjecture with
> finite wreath product* if for any finite group $F$ the wreath product $G \wr F$ satisfies the
> $K$- and $L$-theoretic Farrell-Jones Conjecture (with respect to the family of virtually cyclic
> subgroups).

> Since the class of CAT(0)-groups is closed under finite wreath products, we conclude from
> Example~\ref{ex-astr}~(\ref{ex-astr-2}) that CAT(0)-groups satisfy FJCw.

> **Proposition (Inheritance properties, part 1).** … **Direct products** If $G_1$ and $G_2$
> satisfy FJCw, then the direct product $G_1 \times G_2$ satisfies FJCw.

> **Proof.** Note that [BL12a, Lemma~2.3] also holds for the class $\mathcal{FJ}^K$ of groups
> satisfying the $K$-theoretic Farrell-Jones Conjecture by the remark below the proof of
> [BL12a, Lemma~2.3] and [Weg12, Corollary~1.2]. Therefore, the inheritance properties
> ''subgroups'', ''direct products'', and ''colimits'' are true for FJC (instead of FJCw). …
> **Direct products** This follows from the fact that $(G_1 \times G_2) \wr F$ is a subgroup of
> $(G_1 \wr F) \times (G_2 \wr F)$.

**How it is used.**
- Taking `F` trivial, `G ≀ 1 = G`. So FJCw implies the `K`-theoretic Farrell–Jones conjecture for
  `G` with respect to `VCyc` and every additive `G`-category. That is exactly the hypothesis of
  `cantor-crossed-product-leavitt-tensors-are-k-trivial`.
- **Instances.** `Z^d × F_d'` acts properly and cocompactly on `R^d × (tree)`, which is CAT(0).
  So every `Z^d × F_d'` satisfies FJCw directly, even without the product proposition.
- In the same paper, Example `ex-FJCw-2` states that finitely generated abelian groups are
  CAT(0)-groups and satisfy FJCw.
- **Not checked.** The proofs of [BL12a], [Weg12] and the CAT(0) theorem were not re-derived. The
  journal version was not compared.

## 3. Theorem H: minimal `Z^2`-SFTs of unbounded language complexity

**Statement.**
- **Setup.** Let `T : N -> N` be recursive. For a `Z^2`-SFT `X` over the alphabet `Σ_B`, let
  `L_n(X)` be the set of globally admissible `n × n` patterns.
- **Claim.** There is a minimal `Z^2`-SFT `X` such that, for no constant `C`, is `L_n(X)`
  decidable in time `C·T(Cn) + Cn^2 + C`.

This answers the parenthetical of the w4 need 1fcab928 ("Z^2 minimal SFTs have recursive
languages: is their complexity uniformly bounded?"): no.

### 3.1 Imported: simulation of effective minimal shifts (Durand–Romashchenko, arXiv:1802.01461)

B. Durand and A. Romashchenko, *The expressiveness of quasiperiodic and minimal shifts of finite
type*, arXiv:1802.01461. Read from the e-print TeX source on 2026-09-17. Verbatim:

> **Definition (def:subdynamics).** We say that a shift $\cal A$ on $\mathbb{Z}^{d}$ is
> *simulated* by a shift $\cal B$ on $\mathbb{Z}^{d+1}$ if there exists a projection
> $\pi : \Sigma_B\to \Sigma_A$ such that for every configuration
> $\textbf{f} : \mathbb{Z}^{d+1} \to \Sigma_B$ from $\cal B$ and for all $i_1,\ldots,i_d,j,j'$ we
> have $\pi (\textbf{f}(i_1,\ldots,i_d,j)) = \pi(\textbf{f}(i_1,\ldots,i_d,j'))$ (i.e., the
> projection $\pi$ takes a constant value along each column $(i_1,\ldots,i_d,*)$ …), and the
> resulting $d$-dimensional configuration $\{ \pi(\textbf{f}(i_1,\ldots,i_d,*)) \}$ belongs to
> $\cal A$; moreover, each configuration of $\cal A$ can be represented in this way by some
> configuration of $\cal B$.

> **Theorem (thm-main-min).** (a) For every effective minimal $\mathbb{Z}^d$-shift $\cal A$ there
> exists a minimal SFT $\cal B$ in $\mathbb{Z}^{d+1}$ such that $\cal A$ is simulated by $\cal B$
> in the sense of Definition~\ref{def:subdynamics}.

> in every minimal SFT the set of globally admissible patterns is decidable

In the definition `π` is a map of alphabets, applied cell by cell. The proof of the theorem was
not re-derived.

### 3.2 Sturmian input

- **The shift `Y_α`.** For irrational `α ∈ (0, 1)`, let `Y_α ⊆ {0,1}^Z` be the orbit closure of the
  mechanical word `s_i = ⌊(i+1)α⌋ − ⌊iα⌋`. Its language is the set of factors of the words
  `s_i(ρ) = ⌊(i+1)α + ρ⌋ − ⌊iα + ρ⌋`, `ρ ∈ [0,1)`. `Y_α` is minimal, because it is a coding of
  the minimal rotation by `α`.
- **Ones count.** A factor `w` of length `n` has `Σ w = ⌊(m+n)α + ρ⌋ − ⌊mα + ρ⌋`, which is
  `⌊nα⌋` or `⌊nα⌋ + 1`. Since `nα ∉ Z`, `|Σw / n − α| < 1/n`.
- **Effectivity for computable `α`.**
  - The length-`n` factors are the codings of the open cells into which the `n + 1` points
    `{−iα mod 1 : 0 <= i <= n}` cut the circle.
  - These points are pairwise distinct, since `α` is irrational. So they can be sorted by
    approximating `α` until all gaps are resolved, and the midpoint of each cell can be coded.
  - Hence `L(Y_α)` is decidable, and `Y_α` is effective.
- **Approximation from a decider.** Suppose `L_n(Y_α)` is decidable in time `T_Y(n)`. Enumerate
  the `2^n` words of length `n` until one is accepted, and output `Σw/n`. This approximates `α`
  within `1/n` in time `2^n (T_Y(n) + O(n))`.

### 3.3 Diagonalization

- **The bound `S`.** Let
  `S(n) = 2^(n^3) · n · (max_(m <= n^2) T(m) + n^2)`. This is recursive.
- **The machines.** Fix a list `(e_s)_(s >= 0)` of machine indices in which every index occurs
  infinitely often. Fix an enumeration `(r_s)` of the rationals.
- **The construction.** Build closed rational intervals `I_0 = [1/4, 3/4] ⊇ I_1 ⊇ …`. Let
  `ℓ_s = |I_s|`. At stage `s`:
  1. Choose `n_s > n_(s−1)` with `2/n_s < ℓ_s / 5`.
  2. Run machine `e_s` on input `n_s` for `S(n_s)` steps.
  3. Cut `I_s` into ten closed pieces of length `ℓ_s/10`.
     - If the machine halted with a rational `q`, the open interval `(q − 1/n_s, q + 1/n_s)` has
       length `< ℓ_s/5`, so it meets at most three pieces.
     - The point `r_s` lies in at most two pieces.
  4. Let `I_(s+1)` be the first remaining piece.
- **The limit.** Let `α = ∩ I_s`. It is computable, since the construction is effective and
  `ℓ_s -> 0`. It is irrational, since `α != r_s` for every `s`. And `|α − q_s| >= 1/n_s` whenever
  machine `e_s` halted at stage `s`.
- **The diagonal property.** Suppose some machine `M = e` outputs a rational within `1/n` of `α`
  within `S(n)` steps, for all `n >= n_0`. Pick a stage `s` with `e_s = e` and `n_s >= n_0`. Then
  `M` halts at stage `s` with `|α − q| < 1/n_s`, a contradiction.
- So no machine approximates `α` within `1/n` in time `S(n)` for all large `n`.

### 3.4 Transfer to `Z^2`

- **The SFT.** Apply Theorem thm-main-min(a) to `Y_α`, with `d = 1`. It gives a minimal `Z^2`-SFT
  `X` over `Σ_B`, with a letter map `π`.
- **Row membership.** A word `w` of length `n` is in `L(Y_α)` if and only if some globally
  admissible `n × 1` row pattern `p` of `X` has `π(p) = w`.
  - Every configuration of `Y_α` is the column projection of some configuration of `X`, and
    every column projection lies in `Y_α`.
  - A row pattern is globally admissible if and only if it is the bottom row of some admissible
    `n × n` square.
- **Cost.** A decider for `L_n(X)` in time `T_X(n)` therefore gives
  `T_Y(n) <= |Σ_B|^(n^2) (T_X(n) + O(n^2))`.
- **Conclusion.** Suppose `T_X(n) <= C·T(Cn) + Cn^2 + C`. The resulting approximation time is at
  most `2^n |Σ_B|^(n^2) (C·T(Cn) + O(n^2))`. For all sufficiently large `n` this is at most `S(n)`:
  - `2^n |Σ_B|^(n^2) <= 2^(n^3)` once `n > log_2|Σ_B| + 1`;
  - `C·T(Cn) <= n · max_(m <= n^2) T(m)` once `n >= C`;
  - `O(n^2) <= n · n^2`.

  This contradicts Section 3.3. ∎
- **Why constants do not help.** The alphabet `Σ_B` depends on `α`, which is built after `S`.
  That is why `S` dominates every `c^(n^2)`, and why the diagonalization defeats each machine
  infinitely often rather than once.

**Caveats.**
- Theorem H says nothing about freeness or quantum rigidity of `X`.
- For minimal abelian actions the trivially acting subgroup is the stabilizer of every point.
  - A vector `(a, b)` fixing a configuration of `X` makes its projected configuration of `Y_α`
    `a`-periodic, so `a = 0`. So the kernel is contained in `0 × Z`. It could be nontrivial.
  - So `X` need not be free.
- Quantum rigidity (`sft-crossed-product-fp-iff-quantum-rigid`) of Durand–Romashchenko SFTs is not
  known.
- The complexity prerequisite of Attempt 6 is therefore met only in the form "hard minimal
  `Z^2`-SFTs exist". The combined form "hard, free, minimal and quantum rigid" remains open.

## 4. Reduction R1

**Open claim `decidable-algebras-embed-in-z2-sft-boundary-product-hosts`.** For
every finitely generated `G` with solvable word problem there are:
- a free minimal `Z^2`-SFT `Ω` over `F_2` with `B_Ω = LC(Ω, F_2) ⋊ Z^2` finitely presented;
- some `d >= 2`;
- a unital embedding `F_2[G] -> B_Ω ⊗ L_∂(d)`.

**Route to the target.**
- `free-minimal-crossed-products-are-simple-with-rank-models`(1) makes `B_Ω` simple with centre
  `F_2`.
- `Z^2` is torsion-free and CAT(0), so it satisfies FJCw (Section 2). So `(Z^2, Ω)` is a valid host.
- Theorem P makes `(Z^2 × F_d, Ω × ∂F_d)` a valid host with algebra `B_Ω ⊗ L_∂`, which contains
  `F_2[G]`.
- FJCw gives the target's Farrell–Jones hypothesis (Section 2).

**Why this is a decomposition that can fail in parts.**
- (Q) Existence of even one free minimal quantum rigid `Z^2`-SFT over `F_2`
  (`free-minimal-z2-sft-is-quantum-rigid`, `F_2` form) is necessary for the open claim.
- (H) The SFTs used must have no uniform recursive language bound. The table argument sketched in
  artifact `fp-crossed-product-shape-free-group-kill-2026-09-17`, Section 7, applies over
  `Z^2 × F_d`, whose word problem is linear. This is only a sketch there.
- (E) The embedding itself.
- Unlike the bare `Z^2` case, (E) does not force `F_2`-linear soficity of `G` through a rank model
  (Theorem P.3).

## 5. Reduction R2 (group level)

**Open claim `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units`.** For every
finitely generated `G` with solvable word problem there are a valid host `(P, X)` over `F_2`, with
algebra `B`, and an injective homomorphism `G -> (B ⊗ L)^x`, where `L = L_(F_2)(1,2)`.

**Route to `boone-higman-conjecture`.** Put `R = B ⊗ L`.
1. `cantor-crossed-product-leavitt-tensors-are-k-trivial`(1) gives `K_1(R) = K_2(R) = 0`, since FJCw
   implies its hypothesis.
2. `leavitt-tensor-hosts-acyclic-steinberg-and-fp`(3) makes `R^x` finitely presented, because `B`
   is simple and finitely presented. This step is conditional on Khanh arXiv:2609.08428v1.
3. `central-simple-leavitt-tensor-unit-groups-are-simple`(2) makes `R^x` simple, because `B` is
   central simple.
4. So `G <= R^x`, which is finitely presented and simple.

**Relation to the target.**
- The target implies the open claim: `G <= F_2[G]^x <= B^x <= R^x`.
- The open claim asks for less. `G` may use:
  - `GL_n(B) ≅ GL_1(M_n(B))`, which lies in `R^x` through `M_n(F_2) ⊆ L`, since `L ≅ M_n(L)`;
  - Thompson-like elements built from the Leavitt isometries;
  - their products with `B^x`.
- The unit groups `R^x` are finitely presented and simple, so for a fixed host the open claim is an
  embedding problem into one Boone–Higman container. The family must still have unbounded
  word-problem complexity (`complexity-bounded-host-classes-are-not-universal`).

## 6. Not checked

- The proofs behind Wegner's inheritance properties and the CAT(0) theorem.
- The Durand–Romashchenko construction.
- Whether Durand–Romashchenko SFTs can be made free. Whether any hard minimal `Z^2`-SFT is quantum
  rigid.
- Whether (E) holds for any non-linear-sofic decidable group.
