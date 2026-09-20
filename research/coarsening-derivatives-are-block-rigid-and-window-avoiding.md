---
rg: 2
id: coarsening-derivatives-are-block-rigid-and-window-avoiding
kind: claim
title: "Every coarsening derivative datum on the tree F-set is a locally constant, window-avoiding leaf-interval partition, and x0-segments in its good set force many blocks"
distinct_from:
  thompson-f-trees-carry-an-ackermann-derivative-hierarchy: that is the open existence statement H_k; this is a normal form for every coarsening candidate (the class containing Moore's derivative and all ratio variants), turning H_k for that class into a colouring problem and proving a lower bound on the size of the derivative of Folner-typical trees.
  marginal-derivative-amplification-is-sharp-at-log-height: that bounds the height any derivative datum certifies; this describes what a coarsening datum on trees is, combinatorially, and bounds |dT| from below on Folner mass without iterating.
artifacts:
  - experiments/coarsening-block-rigidity-2026-09-17/check_block_rigidity.py
  - experiments/coarsening-block-rigidity-2026-09-17/output.txt
---

**ESTABLISHED** by `coarsening-derivatives-block-rigidity-proof` (not yet refereed).

**Setting.** As in `marginal-derivative-amplification-is-sharp-at-log-height`.
- `𝒯` is the set of finite rooted binary trees (complete prefix codes, i.e. sets of leaves)
  with Moore's partial right action of `F` (arXiv:0905.1118v7, Sec. 2 and 4);
  `Γ = {x0^±1, x1^±1}`; `T/u` is the subtree below the node `u`; `|T|` is the leaf count.
- A derivative datum `(∂, A)` satisfies (E′): for `T ∈ A`, `γ ∈ Γ`, `T·γ` is defined iff
  `∂T·γ` is defined, and then `∂(T·γ) = ∂T·γ`. `B = 𝒯 ∖ A` is `c`-thin if `μ(B) ≤ c·bd(μ)`.
- The datum is **coarsening** if `∂T` is dominated by `T` for every `T ∈ A` (every leaf of
  `∂T` has an extension in `T`). Moore's `∂` (his Def. 5.1) and every datum in
  `tree-grafting-inflations-kill-superlinear-ratio-derivatives` are coarsening.
- For `U` dominated by `T` with leaves `u_1 <_lex … <_lex u_m`, the **block partition**
  `π(T,U)` is the partition of the leaf indices `{0,…,|T|−1}` into the `m` consecutive
  intervals of leaves of `T` below `u_1, …, u_m`, and the **decoration** is
  `β(T,U) = (T/u_1, …, T/u_m)`. So `T = σ_β(U)` is `U` with `T/u_i` grafted at `u_i`.
- The **window** is `W = {∅, 0, 1, 10, 11}`. `U` is **window-avoiding for `T`** if no leaf
  `u ∈ W` of `U` has `|T/u| ≥ 2`.

**Theorem 1 (window lemma).** For `U` dominated by `T`, the following are equivalent:
- `T·γ` is defined iff `U·γ` is defined, for every `γ ∈ Γ`;
- `U` is window-avoiding for `T`, or `(U, T) = ({∅}, {0,1})`.

So the definedness half of (E′) is exactly window avoidance, for every coarsening datum.

**Theorem 2 (block rigidity).** Let `(∂, A)` be coarsening, `T ∈ A`, `γ ∈ Γ` with `T·γ`
defined. Then `π(T·γ, ∂(T·γ)) = π(T, ∂T)` and `β(T·γ, ∂(T·γ)) = β(T, ∂T)`, whether or not
`T·γ ∈ A`. Hence:
1. On each connected component of the Schreier graph restricted to `A`, the pair `(π, β)`
   is constant, and `∂` is the injective map `σ_β(V) ↦ V` onto its image.
2. Conversely, a coarsening map `∂` satisfies (E′) at `T` iff `∂T` is window-avoiding for `T`
   (or the exceptional pair) and `π(T·γ, ∂(T·γ)) = π(T, ∂T)` for every `γ` with `T·γ`
   defined.

So a coarsening datum is the same thing as a **colouring** `T ↦ π(T)` of each level `𝒯_n`
by leaf-interval partitions that are window-avoiding block partitions, with `A` a set on
which the colouring is constant along every edge leaving `A`.

**Theorem 3 (spine count).** Let `(∂, A)` be coarsening. If `T, T·x0, …, T·x0^{ℓ−1}` are all
defined and in `A` (successive single steps), then `|∂T| ≥ ℓ − 1`.

**Corollary 4 (Følner-typical derivatives are large).** Let `(∂, A)` be coarsening with
`B` `c`-thin. For every finitely supported `μ ≥ 0` and every `ℓ ≥ 1`,
`μ({T ∈ A : |∂T| ≥ ℓ − 1}) ≥ μ(𝒯) − (c + (ℓ − 1)(c + 1))·bd(μ)`.
In particular, if `μ` is weighted `ε`-Følner, more than half of its mass lies on trees with
`|∂T| ≥ ⌊1/(2(c+1)ε) − c/(c+1)⌋`, i.e. `|∂T| ≥ Ω_c(1/ε)`.

**Proposition 5 (pointwise satisfiability).** Fix `m ≥ 6`, a tree `V ∈ 𝒯_m` on which all
of `Γ` is defined (the set `Full_m`), any decoration `β = (P_1, …, P_m)`, and put
`S = σ_β(V)`. Then `V` is a window-avoiding coarsening of `S`, `S·γ` is defined for all
`γ ∈ Γ`, and `σ_β(V·γ) = S·γ`. So `∂(σ_β(V')) := V'` on `σ_β(𝒯_m)` satisfies (E′) at every
point of `σ_β(Full_m)`. Since `|S| = Σ|P_i|` is arbitrary, the conditions
"block partition", "window avoidance", "(E′) along edges inside a decoration class" and
"`|S| ≥ ψ(|∂S|)`" are simultaneously satisfiable for every `ψ` at every tree of the form
`σ_β(V)`.

**What this means for `H_k`.**
- A pointwise refutation (showing inflated trees lie in `B`, as in
  `tree-grafting-inflations-kill-superlinear-ratio-derivatives`) must use a defining
  condition beyond these four, such as a subtree ratio. By Proposition 5 no such argument
  can refute the contraction requirement of `H_k` itself within the coarsening class.
- What remains is global: `B` must contain the interfaces of the colouring `π`. By
  Corollary 4 the colours on `ε`-Følner mass have `Ω(1/ε)` blocks, so contraction
  `|T| ≥ Ack_k(|∂T|)` gives Følner trees of size `≥ Ack_k(Ω(1/ε))` in one step. That is
  weaker than Theorem A of the amplification node, `Ack_{k+1}(Ω(log 1/ε))`, so there is no
  contradiction. A kill of coarsening `H_k` needs an upper bound on `|T|` against `ε` on
  Følner mass, which is a Følner-function upper bound for `F`.

**Computation.** `experiments/coarsening-block-rigidity-2026-09-17/check_block_rigidity.py`
(output in `output.txt`) checks Theorem 1 on all 33268 dominated pairs `(T, U)` with
`|T| ≤ 9`, Theorem 2 on all 54492 defined edges of those pairs, and Theorem 3 on all 4861
`x0`-segments of trees with `≤ 9` leaves, minimizing over all admissible constant
partitions. The theorems do not depend on it.
