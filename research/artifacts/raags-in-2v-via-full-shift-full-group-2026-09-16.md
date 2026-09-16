# Right-angled Artin groups in 2V through the full shift (2026-09-16)

Lane: swarm-zaremsky-2-19-embeddings-into- (unreviewed). Targets:

- `full-shift-topological-full-group-embeds-in-2v` (Part A),
- `every-raag-embeds-in-full-shift-topological-full-group` (Part B),
- `every-raag-embeds-in-brin-thompson-group-2v` and
  `z3-free-z-embeds-in-brin-thompson-group-2v` (Part C),
- `virtually-special-groups-embed-in-brin-thompson-group-2v` (Part D).

Part E proves a limit of the method, and Part F is the literature audit.

## Status and credit

**The results of Parts A–C are not new.** V. Salo, *Graph and wreath products
in topological full groups of full shifts*, arXiv:2103.06663v1 (11 Mar 2021;
still the only arXiv version on 2026-09-16, with no journal reference).

- **Abstract**, verbatim from the arXiv source: "The group $\llb X \rrb$ embeds in
  the higher-dimensional Thompson group $2$V, so it follows that $2$V contains
  all RAAGs, refuting a conjecture of Belk, Bleak and Matucci."
- **Introduction:** "In this paper, we refute the conjecture from \cite{BeBlMa20}
  and completely settle the issue of RAAG embeddability: all (countable) RAAGs
  embed in $n$V for all $n \geq 2$."
- **Section 2:** Salo defines 2V as maps of `{0,1}^Z` of the form
  `f(xu.vy) = xu'.v'y`. The Lemma "$\llb \{0,1\}^\Z \rrb \leq 2\mathrm{V}$" is
  introduced with "The way the definitions are stated, the following is
  obvious."
- **Section 3:** the Theorem "For every alphabet $\Sigma$, every RAAG embeds in
  $\llb \Sigma^\Z \rrb$", followed by "This includes the case of RAAGs defined
  by a countably infinite graph." Salo derives it from a graph-product theorem
  (Theorem thm:GraphProducts) proved with conveyor belts.

The conjecture refuted is Belk–Bleak–Matucci, arXiv:1602.08635v1, Conjecture
1.7: "A right-angled Artin group A_Γ embeds into nV if and only if A_Γ does not
contain Z^(n+1) * Z." This repository recorded its case `n = 2` as the open claim
`z3-free-z-does-not-embed-in-2v`.

**What this artifact adds.** Salo's paper is an unrefereed preprint and proves
more general statements. So Parts A and B give complete, self-contained proofs
of exactly what the graph uses, for finite graphs Γ.

- Part A spells out the "obvious" lemma against the brick definition of 2V, and
  handles the dyadic-subdivision issue.
- Part B specialises Salo's conveyor-belt construction for graph products to
  vertex groups `Z`: one belt type per vertex, and shared cells only between
  belts of non-adjacent types. Two things come from Salo's proof of Theorem
  thm:GraphProducts: a cell shared between neighbouring belts of non-commuting
  types, and the greedy non-commuting chain taken from the right end of a
  reduced word. The specialisation is this lane's own: one `T` cell and one `B`
  cell per block, the shared cell always on the next block's `T` letter, the
  explicit window `x_[-4,3]`, and the complete verification. (Referee
  correction 2026-09-16: an earlier draft said Part B "borrows only the idea of
  belts and of moving a head". That understated the overlap with Salo.)
- Part B is checked exactly by
  `experiments/raag-conveyor-belts-full-shift-2026-09-16/belts.py` (Part B.6).

## Conventions

- `C = {0,1}^N` is the Cantor set of one-sided infinite words, and `wC` is the
  cylinder of a finite word `w`.
- A *dyadic brick* of `C^2` is `w_1 C × w_2 C`. The *canonical map*
  `w_1C × w_2C → w_1'C × w_2'C` is `(w_1 a, w_2 b) ↦ (w_1' a, w_2' b)`.
- **2V.** `2V` is the group of homeomorphisms `F` of `C^2` for which there are a
  dyadic subdivision `D_1, …, D_s` of `C^2` and a second one `R_1, …, R_s` with
  `F` canonical from `D_i` onto `R_i` for each `i`. Here a *dyadic subdivision*
  is a partition obtained from `C^2` by repeatedly halving a brick in one
  coordinate.
  - This is Brin's definition, as recalled in arXiv:1602.08635 §3.
  - The looser reading, where any finite partition into bricks is allowed,
    gives a group containing this one. So Part A proves membership for the
    stricter reading, which covers both.
- `Σ^Z` is a two-sided full shift with shift `σ(x)_i = x_{i+1}`. Then
  `[[Σ^Z]]` is the group of homeomorphisms `f` of `Σ^Z` such that
  `f(x) = σ^{c(x)} x` for a continuous `c : Σ^Z → Z`, the *cocycle*.
  - The cocycle is unique: on the dense set of aperiodic points `c(x)` is forced,
    and `c` is continuous.
  - By compactness `c` is locally constant and takes finitely many values.

## Part A. `[[{0,1}^Z]]` embeds in `2V`

Let `X = {0,1}^Z` and `Φ : C^2 → X`, `Φ(a, b) = … b_2 b_1 b_0 . a_0 a_1 a_2 …`.
That is, `Φ(a,b)_i = a_i` and `Φ(a,b)_{-1-i} = b_i` for `i ≥ 0`. `Φ` is a
homeomorphism, so `f ↦ F = Φ^{-1} f Φ` is an injective homomorphism
`Homeo(X) → Homeo(C^2)`. It remains to show `F ∈ 2V` for `f ∈ [[X]]`.

**Uniform window.** Let `f ∈ [[X]]` have cocycle `c`. By uniform continuity there
is `r ≥ 1` such that:

- `|c| ≤ r`, and
- `c(x)` depends only on `x_{[-r, r-1]}`.

For words `u = u_{-r} … u_{-1}` and `v = v_0 … v_{r-1}`, let `[u.v]` be the
cylinder where those coordinates are `u` and `v`. Then
`Φ^{-1}[u.v] = vC × u^R C`, where `u^R = u_{-1} u_{-2} … u_{-r}`. These `4^r`
bricks form the uniform grid `G_r`, which is a dyadic subdivision.

**Each grid brick maps canonically.** Fix `Q = [u.v]` with `c ≡ k` on `Q`, and
write `x = y u . v z ∈ Q` with `y` left-infinite and `z` right-infinite.

- **`0 ≤ k ≤ r`.** `σ^k x = y u v_0…v_{k-1} . v_k … v_{r-1} z`. In coordinates,
  `F(vz, u^R w) = (v_{[k,r)} z, v_{k-1}…v_0 u^R w)` for all `z, w ∈ C`. So `F`
  is canonical from `vC × u^R C` onto `v_{[k,r)}C × (v_{[0,k)})^R u^R C`.
- **`k = -m`, `0 < m ≤ r`.** `σ^{-m} x = y u_{-r}…u_{-m-1} . u_{-m}…u_{-1} v z`.
  So `F(vz, u^R w) = (u_{-m}…u_{-1} v z, u_{-m-1}…u_{-r} w)`. This is canonical
  from `vC × u^R C` onto `u_{[-m,-1]} v C × (u_{[-r,-m)})^R C`, since `u^R`
  begins with `(u_{[-m,-1]})^R`.

In both cases the image brick `R_Q = F(Q)` has prefix lengths `(r-k, r+k)`. Both
lie between `0` and `2r`.

**Making both partitions dyadic subdivisions.** `F` is a bijection, so the image
bricks `R_Q` partition `C^2`, but a priori they need not form a dyadic
subdivision. Refine as follows.

- Every `R_Q` has both prefix lengths `≤ 2r`, so it is a union of cells of the
  uniform grid `G_{2r}`.
- A cell `E ⊆ R_Q` of `G_{2r}` has prefixes `(q_1 s_1, q_2 s_2)`, where
  `(q_1, q_2)` are the prefixes of `R_Q`, `|s_1| = r+k` and `|s_2| = r-k`.
- The canonical map from `Q` onto `R_Q` restricts to a canonical map from the
  brick `F^{-1}(E) = v s_1 C × u^R s_2 C` onto `E`.
- The bricks `F^{-1}(E)` with `E ⊆ R_Q` are the uniform subdivision of `Q` by
  `r+k` halvings in coordinate 1 and `r-k` halvings in coordinate 2.
- Hence `{F^{-1}(E) : E ∈ G_{2r}}` is obtained from `C^2` by iterated halving:
  first to `G_r`, then inside each `Q`.

`F` maps each of these bricks canonically onto a cell of `G_{2r}`, which is
itself a dyadic subdivision. So `F ∈ 2V`, and `[[X]] ≅ Φ^{-1}[[X]]Φ ≤ 2V`. ∎

## Part B. Every finite-graph RAAG embeds in `[[{0,1}^Z]]`

Let `Γ` be a finite simple graph with vertex set `V`, `|V| = N ≥ 1`. Write
`u ~ w` when `{u, w}` is an edge; this forces `u ≠ w`. The RAAG is
`A_Γ = ⟨ t_u (u ∈ V) | [t_u, t_w] = 1 for u ~ w ⟩`.

### B.1 Head maps

Let `Σ` be any finite alphabet and `f ∈ [[Σ^Z]]` with cocycle `c`. For `x ∈ Σ^Z`,
define the *head map* `p^f_x : Z → Z`, `p^f_x(i) = i + c(σ^i x)`.

- **(P1) Composition.** `p^{fg}_x = p^f_x ∘ p^g_x`.
  - The function `y ↦ c_g(y) + c_f(σ^{c_g(y)} y)` is continuous and shifts
    `y` to `fg(y)`, so by uniqueness it is `c_{fg}`.
  - Then `p^{fg}_x(i) = p^g_x(i) + c_f(σ^{p^g_x(i)} x) = p^f_x(p^g_x(i))`.
  - In particular `p^{f^{-1}}_x = (p^f_x)^{-1}`, and every `p^f_x` is a
    bijection.
- **(P2) Construction.** Suppose `c : Σ^Z → Z` is continuous and `p_x(i) = i + c(σ^i x)` is a
  bijection of `Z` for every `x`. Then `f(x) = σ^{c(x)} x` lies in `[[Σ^Z]]`.
  - *Injective.* If `f(x) = f(y)`, then `y = σ^j x` with `j = c(x) - c(y)`. So
    `p_x(j) = j + c(y) = c(x) = p_x(0)`, which gives `j = 0`.
  - *Surjective.* If `j = p_x^{-1}(0)`, then `f(σ^j x) = σ^{p_x(j)} x = x`.
  - A continuous bijection of a compact Hausdorff space is a homeomorphism.
- **(P3) Detecting nontriviality.** If `p^f_x(i) ≠ i` for some `x, i`, then
  `c(σ^i x) ≠ 0`, so `c ≢ 0` and `f ≠ id`, because the cocycle of `id` is `0`
  by uniqueness.

### B.2 Blocks, belts and the generators

- **Alphabet.** `Σ = {T_u, B_u : u ∈ V} ∪ {#}`.
- **Blocks.** A *`u`-block* of `x` at position `i` means `x_i x_{i+1} = T_u B_u`.
  Blocks never overlap, since no letter is both a `T` letter and a `B` letter.
- **Belts.** A *`u`-belt* is a maximal run of `u`-blocks at consecutive positions
  `a, a+2, a+4, …`. It may be finite, one-sided infinite, or bi-infinite, and
  every `u`-block lies in exactly one `u`-belt.

**Cells of a finite belt.** Let the belt `β` have blocks at `a, a+2, …, e`, with
`e = a + 2(L-1)`.

- `T_k = a + 2(k-1)` for `1 ≤ k ≤ L`, and `B_k = a + 2k - 1` for `1 ≤ k < L`.
- **Relocation.** If `x` has a `w`-block at `e+2` with `w ≠ u` and `w ≁ u`, the
  belt is *relocated*: `B_L = e + 2`, the `T` letter of that `w`-block.
  Otherwise `B_L = e + 1`.
- The cell set is `C(β) = {T_1, …, T_L, B_1, …, B_L}`. The map `π_β` is the
  `2L`-cycle `T_1 → T_2 → … → T_L → B_L → B_{L-1} → … → B_1 → T_1`.

**Infinite belts.** The same formulas define `C(β)` and a bijection `π_β` of
`C(β)` without fixed points: `T` cells move right and `B` cells move left.

- A left-infinite belt has a last block and may be relocated. Its cells form
  one bi-infinite orbit `… → T_{L-1} → T_L → B_L → B_{L-1} → …`.
- A right-infinite belt has a first block. Its cells form one bi-infinite orbit
  `… → B_2 → B_1 → T_1 → T_2 → …`.
- A bi-infinite belt has `T ↦ T+2` and `B ↦ B-2`, so its cells form two
  bi-infinite orbits (the `T` letters and the `B` letters).

**Distinct `u`-belts have disjoint cell sets.**

- The `T` cells and unrelocated `B` cells of `β` are letters of `β`'s own blocks.
- A relocated `B_L` is the `T` letter of a block of another type, so it is not a
  letter of any `u`-block.
- Two belts relocated onto the same position `e+2` would both have their last
  block at `e`, so they would be the same belt.

**Definition of `f_u`.** Let `p^{(u)}_x` be `π_β` on `C(β)` for every `u`-belt
`β` of `x`, and the identity elsewhere. It is a bijection of `Z`. The belt
structure of `σ^i x` is that of `x` translated by `-i`. Hence
`p^{(u)}_{σ^i x}(j) = p^{(u)}_x(i+j) - i`, and `c_u(x) := p^{(u)}_x(0)` satisfies
`i + c_u(σ^i x) = p^{(u)}_x(i)`.

**Explicit rule.** `c_u(x)` depends only on `x_{[-4,3]}`. Here "`w` non-adjacent"
means `w ≠ u` and `w ≁ u`.

1. **`x_0 x_1 = T_u B_u`.** The head is on `T_k`.
   - If `x_2 x_3 = T_u B_u`, then `c_u = +2` (to `T_{k+1}`).
   - Else, if `x_2x_3 = T_w B_w` with `w` non-adjacent, then `c_u = +2` (to the
     relocated `B_L`).
   - Else `c_u = +1` (to the unrelocated `B_L`).
2. **`x_{-1} x_0 = T_u B_u`.** The head is on the `B` letter of a `u`-block.
   - If `x_1 x_2 = T_w B_w` with `w` non-adjacent, then `c_u = 0`: this `B`
     letter was relocated away and is not a cell.
   - Else, if `x_{-3} x_{-2} = T_u B_u`, then `c_u = -2` (`B_k → B_{k-1}`).
   - Else `c_u = -1` (`B_1 → T_1`).
3. **`x_0 x_1 = T_w B_w` with `w` non-adjacent, and `x_{-2} x_{-1} = T_u B_u`.**
   The head is on the relocated `B_L` of the `u`-belt whose last block is at
   `-2`.
   - If `x_{-4} x_{-3} = T_u B_u`, then `c_u = -3` (to `B_{L-1}`).
   - Else `c_u = -2` (`L = 1`, to `T_1`).
4. **Otherwise** `c_u = 0`.

The three hypotheses `x_0 = T_u`, `x_0 = B_u` and `x_0 = T_w` with `w ≠ u` are
mutually exclusive, and together they reach every cell. So `c_u` is continuous
and every `p^{(u)}_x` is a bijection. By (P2), `f_u(x) := σ^{c_u(x)} x` lies in
`[[Σ^Z]]`, and `p^{f_u}_x = p^{(u)}_x`.

### B.3 Relations

Let `u ~ w`. No `u`-belt is relocated onto a `w`-block and no `w`-belt onto a
`u`-block, because relocation needs non-adjacent types. Suppose a position `P`
were a cell of both a `u`-belt and a `w`-belt. The cases:

- **`P` is a letter of a `u`-block and of a `w`-block.** Impossible, since
  `u ≠ w`.
- **`P` is a letter of a `u`-block and a relocated cell of a `w`-belt.** Then
  `P` is the `T` letter of a block whose type is non-adjacent to `w`, and that
  type is `u ~ w`. Contradiction. The symmetric case is the same.
- **`P` is a relocated cell of both.** Both belts have their last block at
  `P - 2`, which has a single type. Contradiction.

So `p^{(u)}_x` and `p^{(w)}_x` are bijections with disjoint supports, each
preserving its own support, and they commute. By (P1) and (P3),
`[f_u, f_w] = id`. Hence `t_u ↦ f_u` extends to a homomorphism
`Ψ : A_Γ → [[Σ^Z]]`.

### B.4 Faithfulness

**Syllables.** Write `g ∈ A_Γ` as `s_1 s_2 ⋯ s_ℓ` with `s_i = t_{j_i}^{n_i}` and
`n_i ≠ 0`. Call the expression *reduced* if there are no `i < m` with `j_i = j_m`
and `j_q ~ j_i` for all `i < q < m`.

**Lemma 1.** Every `g ≠ 1` has a reduced expression with `ℓ ≥ 1`.

*Proof.* Take an expression with `ℓ` minimal. If `i < m` violate reducedness,
then `s_m` commutes with every `s_q` for `i < q < m`, so it can be moved next to
`s_i` and merged into `t_{j_i}^{n_i + n_m}`. The merged syllable is dropped if
the exponent is `0`. This gives fewer syllables, contradicting minimality. Also
`ℓ ≥ 1` because `g ≠ 1`. ∎

**Lemma 2 (greedy chain).** Let `s_1 ⋯ s_ℓ` be reduced. Put `c_1 = ℓ`. Given
`c_q`, let `c_{q+1}` be the largest `m < c_q` with `j_m ≁ j_{c_q}`, allowing
`j_m = j_{c_q}`, and stop when there is none. Relabel the chain increasingly as
`i_1 < i_2 < ⋯ < i_k = ℓ`. Then:

1. `j_{i_{p-1}} ≠ j_{i_p}` and `j_{i_{p-1}} ≁ j_{i_p}`;
2. every `m` with `i_{p-1} < m < i_p` has `j_m ~ j_{i_p}`;
3. every `m < i_1` has `j_m ~ j_{i_1}`.

*Proof.* Items 2 and 3 are the definition of the greedy step and of its stopping
condition. For item 1, suppose `j_{i_{p-1}} = j_{i_p}`. By item 2, all syllables
strictly between have types adjacent to it, which contradicts reducedness. ∎

**Theorem.** `Ψ` is injective.

*Proof.* Let `g ≠ 1` have a reduced expression, with chain `i_1 < ⋯ < i_k` as in
Lemma 2. Set `u_p = j_{i_p}` and `L_p = |n_{i_p}|`.

**The configuration.** Let
`x = ⋯ # # β_1 β_2 ⋯ β_k # # ⋯`, where `β_p = (T_{u_p} B_{u_p})^{L_p}`.

- Consecutive types differ, and `x` is `#` outside the belts, so each `β_p` is
  a maximal `u_p`-belt, and these are all the belts of `x`.
- Since `u_p ≁ u_{p+1}`, the belt `β_p` is relocated for `p < k`:
  `B_{L_p}(β_p) = T_1(β_{p+1})`.
- `β_k` is followed by `#`, so it is not relocated.

**Marked positions.** Put `P_p = T_1(β_p)` for `1 ≤ p ≤ k`, and
`P_{k+1} = B_{L_k}(β_k)`.

- For `2 ≤ p ≤ k`, `P_p` is a cell of exactly the belts `β_p` (type `u_p`) and
  `β_{p-1}` (type `u_{p-1}`).
- `P_1` is a cell of `β_1` only, and `P_{k+1}` of `β_k` only.

**One chain syllable.** `π_{β_p}` is a `2L_p`-cycle, so
`π_{β_p}^{L_p} = π_{β_p}^{-L_p}` sends `B_{L_p}` to `T_1`. Note that `P_{p+1}` is
`B_{L_p}(β_p)` for every `p ≤ k`. Hence `p^{f_{u_p}^{n_{i_p}}}_x(P_{p+1}) = P_p`.

**Other syllables.** Let `i_{p-1} < m < i_p`, or `m < i_1` when `p = 1`. Then
`j_m ~ u_p` by Lemma 2, so `j_m ≠ u_p`, and `j_m ≠ u_{p-1}` because
`u_{p-1} ≁ u_p`. So `P_p` is not a cell of any `j_m`-belt, and
`p^{f_{j_m}^{n_m}}_x(P_p) = P_p`.

**The whole word.** By (P1), `p^{Ψ(g)}_x = p^{Ψ(s_1)}_x ∘ ⋯ ∘ p^{Ψ(s_ℓ)}_x`, with
`s_ℓ` applied first. Start at `P_{k+1}`:

- `s_ℓ = s_{i_k}` moves it to `P_k`;
- the syllables strictly between `i_{k-1}` and `i_k` fix it;
- `s_{i_{k-1}}` moves it to `P_{k-1}`, and so on;
- after `s_{i_1}` it is at `P_1`, and the syllables before `i_1` fix it.

So `p^{Ψ(g)}_x(P_{k+1}) = P_1`. Now `P_1` is the leftmost cell of `x` and
`P_{k+1} ≥ P_1 + 1`. By (P3), `Ψ(g) ≠ id`. ∎

### B.5 From `Σ` to the binary shift

- **Padding the alphabet.** Choose `m` with `2^m ≥ 2N + 1` and identify `Σ` with
  a subset of `Σ' = {0,1}^m`. The rules of B.2 never treat the extra letters as
  block letters, so B.2–B.4 go through verbatim over `Σ'`. The configuration of
  B.4 uses letters of `Σ` only. So `A_Γ ≤ [[Σ'^Z]]`.
- **Recoding.** Let `ρ : Σ'^Z → {0,1}^Z` be the concatenation
  `ρ(x)_{mi+q} = (x_i)_q` for `0 ≤ q < m`. It is a homeomorphism with
  `ρ σ = σ^m ρ`. For `f ∈ [[Σ'^Z]]` with cocycle `c`,
  `ρ f ρ^{-1}(y) = σ^{m c(ρ^{-1} y)} y`, whose cocycle is continuous.
- **Conclusion.** `f ↦ ρ f ρ^{-1}` is an injective homomorphism
  `[[Σ'^Z]] → [[{0,1}^Z]]`, so `A_Γ ≤ [[{0,1}^Z]]`. ∎

### B.6 Exact check

`experiments/raag-conveyor-belts-full-shift-2026-09-16/belts.py`, md5
`10719fecd946803b82d892b7669654b6`, run single-threaded in 31 s; the output is
`output.txt` in the same folder. The script implements rules 1–4 over `Σ` plus
one junk letter. It checks the graphs `K_2`, `2K_1`, `P_3`, `K_3 ⊔ K_1` (the
graph of `Z^3 * Z`), `P_4` and `C_4`.

- **Bijectivity and commutation.** Exhaustive over all periodic configurations of
  period `≤ 7` (`N = 2`), `≤ 6` (`N = 3`) and `≤ 5` (`N = 4`), plus 3000 random
  periodic configurations of period 8–60 per graph.
  - Every `p^{(u)}_x` is a bijection.
  - `p^{(u)}_x` and `p^{(w)}_x` commute whenever `u ~ w`.
  - Non-adjacent pairs give non-commuting head maps on thousands of
    configurations.
  - This is valid because for a configuration of period `n`, `p_x` commutes with
    translation by `n`, so it is a bijection of `Z` iff it is a bijection mod `n`.
- **Faithfulness.** Every reduced syllable word of length `≤ 4` with
  `|exponent| ≤ 3` was tested, 305,466 words in all. On its chain configuration
  the head moves from `P_{k+1}` to `P_1`, exactly as in B.4.
- **Normal form.** On 4000 random words per graph the head behaviour agrees with
  the normal form: words reducing to the identity fix the head on random
  configurations, and the others move it on the chain configuration of their
  reduced form.
- **Result:** `ALL OK`. This is evidence for the hand proof, not a replacement
  for it.

## Part C. Consequences

**`A_Γ ≤ 2V ≤ nV` for every finite graph `Γ` and every `n ≥ 2`.** Combine
Parts A and B with `brin-thompson-nv-embeds-in-mv`.

**Belk–Bleak–Matucci Conjecture 1.7 fails for every `n ≥ 2`.** Take `Γ` to be
the complete graph on `n+1` vertices plus an isolated vertex, so
`A_Γ = Z^(n+1) * Z`. Then `A_Γ` embeds in `nV` although it contains
`Z^(n+1) * Z`.

- In particular `Z^3 * Z ≤ 2V` (`z3-free-z-embeds-in-brin-thompson-group-2v`), so
  `z3-free-z-does-not-embed-in-2v` is false and is marked `refuted_by` that
  claim.
- The route `some-gl-n-z-not-in-2v-via-z3-free-z` requires it and becomes
  unusable.
- The `n = 1` case, `Z^2 * Z ≰ V`, is a theorem of Bleak–Salazar-Díaz, as
  quoted in arXiv:1602.08635.

**Effect on Zaremsky 2.19(d).** Every negative answer that goes through a RAAG
inside `GL_N(Z)` is dead. By Part D, so is every negative answer through a
subgroup of `GL_N(Z)` that virtually embeds in a finitely generated RAAG.

- A negative answer to (d) must use a subgroup that is not virtually a subgroup
  of a finitely generated RAAG, such as `H_3(Z)` or an infinite Kazhdan subgroup
  like `SL_3(Z)`.
- `H_3(Z)` virtually embeds in no finitely generated RAAG. Self-contained proof
  from Parts B and E: a finite-index subgroup `H'` of `H_3(Z)` contains `z^m` for
  some `m ≥ 1`, where `z = [a,b]`. The inclusion `H' ≤ H_3(Z)` is a
  quasi-isometry, so `|z^{m k^2}|_{H'} = O(k)` and `z^m` is distorted in `H'`.
  If `H' ≤ A_Γ`, Part B puts `H'` in `[[{0,1}^Z]]`, contradicting E1. (The
  solvable subgroup theorem for CAT(0) groups gives the same conclusion.)

## Part D. Finite extensions; virtually-RAAG groups embed in `2V`

**Lemma D1.** If `H ≤ nV` and `k ≥ 1`, then `H ≀ S_k = H^k ⋊ S_k` embeds in `nV`.

*Proof.* The case `k = 1` is trivial. Let `k ≥ 2`.

- **Pieces.** Take the bricks `Q_i = 1^{i-1}0C × C^{n-1}` for `1 ≤ i < k`, and
  `Q_k = 1^{k-1}C × C^{n-1}`. They form a dyadic subdivision of `C^n` (halve
  repeatedly in coordinate 1).
- **Transport maps.** Let `κ_i : C^n → Q_i` be the canonical map, which inserts
  the prefix in coordinate 1.
- **Local copies.** For `h ∈ nV` let `h^{(i)}` be `κ_i h κ_i^{-1}` on `Q_i` and
  the identity off `Q_i`.
  - If `h` is canonical on the pieces of dyadic subdivisions `(D_j) → (R_j)`,
    then `h^{(i)}` is canonical on the pieces `κ_i(D_j)` together with the
    bricks `Q_{i'}` for `i' ≠ i`.
  - These are again dyadic subdivisions: subdivide `C^n` into the `Q`'s, then
    transport the subdivision of `h` into `Q_i`. So `h^{(i)} ∈ nV`.
- **Permutations.** For `τ ∈ S_k` let `P_τ` be `κ_{τ(i)} κ_i^{-1}` on each `Q_i`.
  It lies in `nV`.
- **The homomorphism.** `P_τ h^{(i)} P_τ^{-1} = h^{(τ(i))}`, and local copies in
  different pieces commute. So `(h_1, …, h_k; τ) ↦ h_1^{(1)} ⋯ h_k^{(k)} P_τ` is
  a homomorphism from `H ≀ S_k`.
- **Injectivity.** Suppose the image is the identity. Each `h^{(i)}` preserves
  every `Q_{i'}`, so `P_τ` preserves every `Q_i`, and `τ = id`. Then each `h_i`
  is the identity. ∎

**Lemma D2 (Kaloujnine–Krasner).** If `N ⊴ G` has finite index `k`, then `G`
embeds in `N ≀ S_k`.

*Proof.* Choose coset representatives `t_1, …, t_k`, so that `G = ⊔ t_i N`.

- For `g ∈ G` write `g t_i = t_{τ_g(i)} n_i(g)` with `n_i(g) ∈ N`. Left
  multiplication by `g` maps the block `t_i N` to the block `t_{τ_g(i)} N` by
  `t_i n ↦ t_{τ_g(i)} n_i(g) n`.
- So `G` acts on `⊔_i N` by permuting blocks and multiplying on the left inside
  blocks. That is a homomorphism into the group of such maps, which is
  `N^k ⋊ S_k = N ≀ S_k`.
- The action is faithful, because left multiplication of `G` on itself is. ∎

**Corollary D3.** If some finite-index subgroup `H` of `G` embeds in `nV`, then
`G` embeds in `nV`.

*Proof.* The normal core `N = ⋂_g gHg^{-1}` has finite index `k` and
`N ≤ H ≤ nV`. By D2 and D1, `G ≤ N ≀ S_k ≤ nV`. ∎

**Corollary D4.** If `G` has a finite-index subgroup that embeds in a finitely
generated RAAG `A_Γ`, then `G ≤ 2V`.

*Proof.* The subgroup lies in `A_Γ ≤ 2V` by Part C, so D3 applies with `n = 2`. ∎

Belk–Bleak–Matucci (arXiv:1602.08635, p. 2) record the same finite-extension
closure through the Bleak–Salazar-Díaz wreath product theorem. D1–D3 above are a
direct proof.

**Examples.** Through `cubulated-hyperbolic-groups-are-virtually-special`, D4
puts every hyperbolic group acting properly and cocompactly on a CAT(0) cube
complex in `2V`, not merely in some `nV`. Likewise it covers every group listed
under `virtually-special-groups-embed-in-some-brin-thompson-group`.

## Part E. A limit of the method: no distortion elements in `[[Σ^Z]]`

**Proposition E1.** Let `Σ` be a finite alphabet and `G ≤ [[Σ^Z]]` a finitely
generated subgroup with finite symmetric generating set `S`. Put
`K = max(1, max_{s ∈ S} ‖c_s‖_∞)`. Every `g ∈ G` of infinite order satisfies
`λ_g := lim_n M(g^n)/n ≥ 1/2` and `|g^n|_S ≥ n/(2K)` for all `n ≥ 1`, where
`M(h) = max_x |c_h(x)|`. In particular `g` is undistorted.

*Proof.*

1. **Subadditivity.** `M(hh') ≤ M(h) + M(h')` by the cocycle identity
   `c_{hh'}(x) = c_{h'}(x) + c_h(σ^{c_{h'}(x)} x)` from (P1). Hence
   `M(h) ≤ K |h|_S`, and by Fekete's lemma `λ_g = lim M(g^n)/n = inf_n M(g^n)/n`
   exists.
2. **An infinite head orbit.** Suppose that for every `x` the orbit of `0` under
   `p^g_x` is finite. The clopen sets `U_j = {x : c_{g^j}(x) = 0}`, `j ≥ 1`, then
   cover `Σ^Z`, so finitely many `U_1, …, U_J` do. For each `x` the orbit of `0`
   then has size `d ≤ J`, and `d` divides `J!`. So `c_{g^{J!}} ≡ 0`, which means
   `g^{J!} = id`. Hence for `g` of infinite order there is `x` whose orbit of `0`
   under `p^g_x` is infinite.
3. **Counting positions.** For that `x`, the positions
   `(p^g_x)^j(0) = p^{g^j}_x(0) = c_{g^j}(x)` for `j = 0, 1, …, n` are pairwise
   distinct, because `p^g_x` is a bijection with no periodic point at `0`. They
   lie in `[-μ_n, μ_n]`, where `μ_n = max_{j ≤ n} M(g^j)`. So `μ_n ≥ n/2`.
4. **Linear growth of `M`.** If `λ_g < 1/2`, choose `ε` with `λ_g < ε < 1/2`
   and `j_0` with `M(g^j) ≤ εj` for `j ≥ j_0`. Then `μ_n ≤ max(C, εn)` with
   `C = max_{j < j_0} M(g^j)`, which contradicts `μ_n ≥ n/2` for large `n`. So
   `λ_g ≥ 1/2`, and since `λ_g` is an infimum, `M(g^n) ≥ n/2` for every `n`.
5. **Conclusion.** `|g^n|_S ≥ M(g^n)/K ≥ n/(2K)`. ∎

Step 4 is the Fekete argument suggested in Salo's commented-out note (below).
The graph already records a stronger established result with a different proof,
`subshift-crossed-product-gl-has-no-distorted-elements`: finitely generated
subgroups of topological full groups of Cantor systems have no distorted
elements of infinite order. E1 is an elementary special case for full shifts.

**Consequences.**

- Groups with a distortion element do not embed in `[[Σ^Z]]` for any `Σ`. These
  include:
  - `H_3(Z)`: `z = [a,b]` has `|z^{n^2}| = O(n)`;
  - `BS(1,2)`: `|s^{2^j}| ≤ 2j + 1`;
  - `SL_3(Z)` and `GL_n(Z)` for `n ≥ 3`, which contain `H_3(Z)`.
- So the full-shift route of Parts A–C cannot answer 2.19(c) or 2.19(d)
  affirmatively. It also cannot put `H_3(Z)` or `BS(1,2)` into `2V`.
- There is no conflict with `brin-thompson-mv-contains-a-distortion-element`:
  distortion in `2V` comes from reversible Turing machines, which move a head
  and also rewrite the tape.
- Salo's source contains, inside a commented-out `\begin{comment}` block titled
  "Restrictions", the line "There are no distortion elements in topological full
  groups" with the proof hint "Apply Fekete's lemma to the maximal value of the
  cocycle of $g^i$". This is not part of the compiled paper. E1 writes out that
  hint in full.

## Part F. Literature audit (2026-09-16)

- **Zaremsky, *Some open problems*** (version of July 12, 2026), Problem 2.19,
  as quoted in `zaremsky-2-19-embeddings-into-brin-thompson-groups`. It says
  "For 2V and up, things remain mysterious" and does not mention RAAGs in 2V.
  Salo's preprint predates the problem's addition date (10/2/24).
- **V. Salo, arXiv:2103.06663v1** (2021-03-11). The arXiv API on 2026-09-16 lists
  v1 only, with no journal reference. A Crossref bibliographic query on
  2026-09-16 found no journal version. It found Salo's separate paper *Graph and
  wreath products of cellular automata* (Internat. J. Algebra Comput., 2024,
  doi 10.1142/s0218196724500553), which is a different paper about automorphism
  groups. The LaTeX source was read on 2026-09-16: abstract, introduction,
  Section 2 definitions and lemma, Section 3 theorems, and the commented
  "Restrictions" block.
- **Belk–Bleak–Matucci, arXiv:1602.08635v1**, Conjecture 1.7 and Theorem 1.1, as
  quoted in `z3-free-z-does-not-embed-in-2v`. Published in Math. Proc. Cambridge
  Philos. Soc. 169(2) (2020) 225–229, per Salo's bibliography; the journal
  version was not checked.
- **Kato, J. Algebra Appl. 17(8) (2018) 1850159.** RAAGs without `Z^d * Z` embed
  in `(d-1)V`. Known here only through Salo's introduction; not fetched.
- **Corwin–Haymaker, Internat. J. Algebra Comput. 26(8) (2016) 1497–1501.** A
  RAAG embeds in `V` iff it does not contain `Z^2 * Z`. Known only through
  Salo's introduction; not fetched.
- **Callard–Salo, arXiv:2208.00685** (distortion elements in `mV`), as imported
  in `brin-thompson-mv-contains-a-distortion-element-citation`.
- **Kojima–Sheng, arXiv:2603.18410v3** (2026-05-23). Abstract only: `nV` is
  torsion locally finite, and contains continuum many copies of `Q` for
  `n ≥ 2`. It says nothing about RAAGs.
- **Bodart–D'Angeli–Perego–Rodaro, arXiv:2608.02111** (2026-08-03). This
  characterises subgroups of `V` through context-free actions and does not
  concern `nV` for `n ≥ 2`.
- **arXiv listing.** A metadata search (all fields "Brin-Thompson", newest first,
  through 2026-03) found no paper disputing Salo's result or claiming a
  counterexample to it.
