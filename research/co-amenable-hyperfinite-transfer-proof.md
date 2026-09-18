---
rg: 2
id: co-amenable-hyperfinite-transfer-proof
kind: route
title: Average Reiter functions of the subgroup's relation over Reiter functions of the coset space, then diagonalize with Borel-Cantelli
target: co-amenable-subgroups-transfer-hyperfinite-orbit-relations
requires: []
---

**Imported, verbatim.** G. Elek and Á. Timár, *Uniform Borel Amenability*, arXiv:2408.12565,
TeX source `rand_submit.tex`, fetched 2026-09-17.

- l.201–206: "Then $\cE$ is \textbf{Borel amenable} if the following two conditions are
  satisfied. (1) For every $n$ there exist non-negative Borel functions
  $\{p_n:\cE\to\R\}_{n=1}^\infty$ such that for all $x\in \X$ we have
  $\sum_{y\equiv_\cE x} p_n(x,y)=1\,,$ and (2) for all pairs $x\equiv_\cE z$:
  $$\lim_{n\to \infty} \sum_{y\equiv_\cE x} |p_n(x,y)-p_n(z,y)|\to 0\,,$$"
- l.296: "$\cE$ is called \textbf{$\mu$-amenable} if there exists a Borel subset $A\subset X$
  with $\mu(A)=1$ such that the restriction $\cE|_A$ of $\cE$ on $A$ is Borel amenable.
  Similarly, $\cE$ is \textbf{$\mu$-hyperfinite} if there exists a Borel subset
  $A\subset X$, $\mu(A)=1$, such that $\cE|_A$ is hyperfinite."
- l.299–300: "\textbf{Connes-Feldman-Weiss Theorem.} Let $\cE$ be a countable Borel equivalence
  relation on $X$ and $\mu$ a Borel probability measure on $X$. Then $\cE$ is $\mu$-amenable
  if and only if it is $\mu$-hyperfinite."
- l.212–214: "$\cE$ is \textbf{hyperfinite} if $\cE=\cup_{i=1}^\infty \cE_i$ for some finite
  equivalence relations $\cE_1\subset \cE_2\subset \cE_3 \subset\dots$ with the property that
  all equivalence classes of $\cE_n$ have bounded size."

Co-amenability is taken as defined by Monod (arXiv:1209.5229, `vn_pnas3.tex` l.371): "A
subgroup $K$ of a group $J$ is called \emph{co-amenable} if there is an $J$-invariant mean on
$J/K$."

**Normalization.** Replace `μ` by an equivalent Borel probability measure (same null sets).
Hyperfiniteness mod null sets and quasi-invariance depend only on the measure class.

**Step 1 (invariant conull set, Reiter functions for `R_H`).** Let `A_0` be conull with
`R_H|A_0 = ∪_n E_n`, where the `E_n` are increasing finite Borel equivalence relations. Set
`A = ∩_{g ∈ G} g A_0`. It is conull, because `G` is countable and preserves null sets, and it
is `G`-invariant. The restrictions `E_n|A` still exhaust `R_H|A`, since `A` is `H`-invariant.
Let `p_n(x, ·)` be the uniform probability on the `E_n|A`-class of `x`. This is Borel,
because the classes are finite and the class-size function of a finite Borel equivalence
relation is Borel (Lusin–Novikov). For `x R_H z` in `A`, the points lie in one `E_n`-class for
large `n`, so `p_n(x, ·) = p_n(z, ·)` eventually. So `R_H|A` is Borel amenable.

**Step 2 (Reiter functions on right cosets).** The bijection `gH ↦ H g^{-1}` turns a
`G`-invariant mean on `G/H` into a mean `m` on `ℓ^∞(H\G)` invariant under right translation.
Fix a finite `K ⊆ G` and `ε > 0`.
- Finitely supported probabilities are weak*-dense in means, so a net `q_i → m` weak*.
- Then `(q_i·k − q_i)_{k∈K} → 0` weakly in `⊕_K ℓ^1(H\G)`, where `(q·k)(D) = q(D k^{-1})`.
- The set `{(q·k − q)_{k∈K}}`, over finitely supported probabilities `q`, is convex. By Mazur
  its norm closure contains `0`.

So there are finitely supported probabilities `q_j` on `H\G`, and finite sets `K_j ↑ G`, with
`‖q_j·g − q_j‖_1 < 1/j` for `g ∈ K_j`.

**Step 3 (averaging).** Fix a section `s : H\G → G`, with `s(D) ∈ D`. For `x ∈ A` and `y ∈ Gx`,
set

`P_{j,n}(x, y) = Σ_D q_j(D) · p_n(s(D) x, y)`.

- Each term is a probability on `H s(D) x ⊆ Gx`, so `P_{j,n}(x, ·)` is a probability on the
  `R_G|A`-class of `x`.
- The sum is finite, so `P_{j,n}` is Borel on `R_G|A`.

For `g ∈ G` and a coset `D'`, write `s(D' g^{-1}) g = h_{D',g} s(D')` with `h_{D',g} ∈ H`. Then

`P_{j,n}(gx, ·) = Σ_{D'} q_j(D' g^{-1}) · p_n(h_{D',g} s(D') x, ·)`,

and the triangle inequality gives

`‖P_{j,n}(gx,·) − P_{j,n}(x,·)‖_1 ≤ ‖q_j·g − q_j‖_1 + e_{j,g,n}(x)`,

`e_{j,g,n}(x) = Σ_{D' ∈ supp(q_j·g)} q_j(D' g^{-1}) ‖p_n(h_{D',g} s(D') x, ·) − p_n(s(D') x, ·)‖_1`.

Here `e_{j,g,n}` is a finite sum of Borel functions. By Step 1 it tends to `0` as `n → ∞` at
every `x ∈ A`, since `s(D')x` and `h_{D',g} s(D') x` are `R_H`-related points of `A`.

**Step 4 (diagonal).**
- Pointwise convergence implies convergence in `μ`-measure. So choose `n_j` with
  `μ{x : max_{g ∈ K_j} e_{j,g,n_j}(x) > 1/j} < 2^{-j}`.
- By Borel–Cantelli there is a conull Borel `B ⊆ A` on which, for each `x` and each `g ∈ G`
  (so `g ∈ K_j` for large `j`), `‖P_j(gx,·) − P_j(x,·)‖_1 ≤ 2/j` eventually, where
  `P_j = P_{j,n_j}`.
- Set `B' = ∩_{g∈G} g B`, which is conull and `G`-invariant. Every pair `x ≡ z` of `R_G|B'`
  has `z = gx` with `x ∈ B'`, so `Σ_y |P_j(x,y) − P_j(z,y)| → 0`.
- The functions `P_j` restricted to `R_G|B'` are Borel, and each `P_j(x,·)` is a probability
  on `[x]_{R_G} ⊆ B'`.

So `R_G|B'` is Borel amenable, hence `R_G` is `μ`-amenable, hence `μ`-hyperfinite by
Connes–Feldman–Weiss. ∎

**Where amenability of `H` was not used.** Only the relation `R_H` enters through the `p_n`,
and only the coset space `H\G` enters through the `q_j`. Stabilizers never appear. That is why
this succeeds where the Zimmer-action version is circular for Thompson's `F`.
