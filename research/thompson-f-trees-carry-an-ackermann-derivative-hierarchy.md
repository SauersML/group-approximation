---
rg: 2
id: thompson-f-trees-carry-an-ackermann-derivative-hierarchy
kind: claim
title: "For every k the tree F-set carries a derivative with thin bad set and Ackermann-k contraction"
distinct_from:
  marginal-derivative-amplification-is-sharp-at-log-height: that proves amplification of any derivative datum is exactly logarithmic in height, and that Moore's datum has exponential contraction; this asks for data on the same F-set with contraction at every level of the Ackermann hierarchy.
  thompson-f-folner-function-exceeds-every-tower: that is Moore's tower bound, which uses one derivative with exponential contraction; this is the structural input needed to go beyond towers.
---

**OPEN.**

**Setting.**
- `𝒯` is the set of finite rooted binary trees, carrying Moore's partial right action of `F`
  (arXiv:0905.1118v7, Section 4).
- `Γ = {x0^±1, x1^±1}`, and `|T|` is the number of leaves.
- The Ackermann levels are `Ack_1(m) = 2m` and `Ack_{k+1}(m) = Ack_k^{(m)}(1)`. So
  `Ack_2(m) = 2^m`, `Ack_3(m) = exp_m(1)`, and every primitive recursive function is eventually
  dominated by some `Ack_k`.

**Statement `H_k`.** There are a map `∂_k : 𝒯 → 𝒯`, a set `A_k ⊆ 𝒯`, and a constant `c_k` such
that:
1. `(∂_k, A_k)` is a derivative datum in the sense of
   `marginal-derivative-amplification-is-sharp-at-log-height`. That is, for `T ∈ A_k` and
   `γ ∈ Γ`, `T·γ` is defined iff `∂_k(T)·γ` is defined, and then `∂_k(T·γ) = ∂_k(T)·γ`.
2. `𝒯 ∖ A_k` is `c_k`-thin: `μ(𝒯∖A_k) ≤ c_k·bd(μ)` for all finitely supported `μ ≥ 0`. For
   example, it may be marginal in Moore's sense.
3. `|T| ≥ Ack_k(|∂_k T|)` for every `T ∈ A_k`.

The claim is: `H_k` holds for every `k`. Since `H_{k+1}` implies `H_k`, it is equivalent to ask
for infinitely many `k`.

**Known levels.**
- `H_{k+1} ⇒ H_k` because `Ack_{k+1} ≥ Ack_k` pointwise.
- Moore's derivative satisfies item 3 with `φ(m) = ⌊2^{m−2}⌋ + 1`. That is `Ack_2` up to a
  bounded shift of the argument, and it is what produces his tower.
- Any datum with `|T| ≥ Ack_k(|∂T| − O(1))` would serve equally well in the route
  `thompson-f-ackermann-folner-via-tree-derivative-hierarchy`.

**Why it matters.**
- *If true.* Combined with the amplification theorem and Moore's Lemmas 3.15 and 4.2, `H_k`
  gives `Føl_F(N) ≥ (Ack_{k+1}(⌊log_{q_k}(1 + 8N/C)⌋) − 2)/3`. So `H_k` for all `k` makes
  `Føl_F` dominate every primitive recursive function: this is
  `thompson-f-folner-function-dominates-every-ackermann-level`.
- *Level 3 alone* gives `Føl_F(N) ≥ Ack_4(Ω(log N))`. That is far beyond every tower of height
  `O(log N)`, which is where Moore's method provably stops.
- *If false for some `k`.* Then no tree derivative of this kind can push lower bounds past
  `Ack_k`. Every derivative argument on `𝒯` then stays inside the primitive recursive range.

**Refutation test.** `H_k` fails for large `k` if, for small `ε`, some weighted `ε`-Følner
measure on `𝒯` is supported on trees of size at most `g(1/ε)`, with `g` primitive recursive.
By Theorem A of `marginal-derivative-amplification-is-sharp-at-log-height`, `H_k` forces a tree
of size `≥ Ack_{k+1}(⌊log_{q_k}(1 + 8/ε)⌋)` in every such support.

**Scope.** Unconditional in both directions: no amenability assumption is made. If `𝒯` itself is
thin, then `H_k` holds vacuously with `A_k = ∅`. That case also forces `F` to be non-amenable, by
Moore's Lemma 4.2.

## Attempts

- **Super-doubling version of Moore's derivative (swarm-0917-w12-w12-f-pull, 2026-09-18).**
  - *Idea:* replace "`2|T/u| ≤ |T/v|` for consecutive interior `u <_lex v`" in Moore's
    Definition 5.1, condition 2, by "`φ(|T/u|) ≤ |T/v|`" with `φ` exponential. Then
    `|T| ≥ φ^{(|∂T|−2)}`, which is `Ack_3`-contraction.
  - *Dies at:* the bad-set marginality, Lemma 5.10 (`𝓔*` is marginal). The only inequality
    that forces the ratio is
    `2|(T·c)/01| = 2|T/001| < |T/01| + |T/10| = |(T·c)/10|`, for `c = x0x1^{-1}`.
    - It comes from merging two consecutive subtrees, each larger than `|T/001|`.
    - An element merging `r` consecutive subtrees gives factor `r`.
    - A marginal decomposition uses finitely many elements, so it forces at most a fixed factor
      `λ`. That gives `φ(m) = λ^m`-type contraction, which is still `Ack_2`.
  - *Invariant:* additivity of leaf count under the merge moves. Each fixed group element
    regroups boundedly many subtrees.
  - Status: heuristic, not a proof of non-marginality.
- **Height-monotone derivative (same agent).**
  - *Idea:* impose that the Moore height `h_∂(T/u)` strictly increases along interior elements.
    Then `|T| ≥ Σ_i φ^{(i)}(4)`, which is `Ack_3`-contraction.
  - *Dies at:* the analogue of Lemma 5.7 (`𝓔` is marginal). Moore uses strict growth under
    regrouping, `|(T·a)/01| = |T/0011| + |T/01| + |T/100| > |T/01|`.
  - For heights, merging subtrees of equal height can keep the height. So the tie set
    `{h(T/001) = h(T/01)}` is not marginalized by `a`, `b` or `x0`.
  - Status: dies at that step. Whether the tie set is thin is untested.
- **Surviving direction.** A weight `w` on subtrees that is strictly superadditive under the
  regrouping moves, `w(T/u ∪ T/v) > w(T/u) + w(T/v)` quantitatively, and grows like
  `Ack_{k−1}` of the leaf count. Leaf count is additive and fails. The parenthesised-word length
  in `F`'s normal form is untested.
- **Leaf-grafting inflations (swarm-0917-w21-w21-f-pull, 2026-09-20; family symbolic-dynamics).**
  - *Result:* the super-doubling death above is now a theorem, proved without marginality
    machinery: `tree-grafting-inflations-kill-superlinear-ratio-derivatives`.
  - *Inflation Lemma:* a one-sided equivariant `σ : 𝒯 → 𝒯` satisfies `bd(σ_*μ) ≤ 2bd(μ)`.
    Examples are `T ↦ δ^{j(|T|)}T` (refine every leaf to depth `j`) and grafting at the `k`-th
    leaf.
  - *Consequence:* a thin bad set must contain at most `2cε` of every inflated Følner measure.
  - *Kill:* take any coarsening derivative (`∂T` dominated by `T`) whose consecutive interior
    leaves satisfy `|T/v| ≥ φ(|T/u|)`, or the mirror, with `sup φ(x)/x = ∞`.
    - (E′) for `x0, x1` forces the crossing pair (last leaf under `01`, first leaf under `10`)
      to be interior.
    - On `δ^{j}T` its size ratio is `< 8|T|`, while its sizes are `≥ 2^{j−3}`.
    - So `B ⊇ δ^{j(·)}(𝒯)`, and `B` is thin only if `F` is non-amenable.
  - *Sharp:* the kill fails at linear `φ`, which is Moore's case. Ratio conditions certify at most
    `Ack_2` contraction non-vacuously.
  - *New necessary condition for `H_k`, `k ≥ 3`:* the good set must be essentially closed under
    grafting inflations.
  - *Survivors:*
    - index-graded ratios `f(i)·|T/u_i| ≤ |T/u_{i+1}|` with `f → ∞`. These are not decided by
      the uniform test, because the index of the crossing pair is unbounded. Neither the
      analogue of Lemma 5.5 nor uniqueness of the maximal `U` (Moore's Lemma 5.2 and condition 3)
      has been checked.
    - conditions on height differences, which shift uniformly under `δ^j`.
- **Normal form for the whole coarsening class (swarm-0917-w23-w23-f-last1, 2026-09-20;
  family reframing).**
  - *Result:* `coarsening-derivatives-are-block-rigid-and-window-avoiding` (ESTABLISHED, with
    a brute-force check to 9 leaves). For every datum with `∂T` dominated by `T`:
    - the definedness half of (E′) is exactly *window avoidance*: no leaf of `∂T` in
      `{∅,0,1,10,11}` carries a nontrivial block;
    - the equivariance half says that the leaf-index interval partition and the block shapes
      are constant along every edge leaving `A`. So a coarsening datum *is* a colouring of each
      level `𝒯_n` by window-avoiding block partitions, and `B` must contain the colouring's
      interfaces;
    - *spine count:* an `A`-segment `T, T·x0, …, T·x0^{ℓ−1}` forces `|∂T| ≥ ℓ − 1`, since each
      left-spine subtree passes through the window node `10`. Hence on every `ε`-Følner measure
      more than half the mass has `|∂T| ≥ Ω_c(1/ε)`.
  - *What it kills:* pointwise inflation kills stop at the contraction requirement. On every
    `σ_β(V)` with `V ∈ Full_m`, block partition, window avoidance, (E′) and `|T| ≥ ψ(|∂T|)` all
    hold together for any `ψ`. So the grafting method of w21 can only refute *extra* defining
    conditions (ratios), never coarsening `H_k` itself.
  - *Where the attempted kill of coarsening `H_3` dies:*
    - The spine count gives Følner trees of size `≥ Ack_k(Ω(1/ε))` in one step. Theorem A
      already gives `Ack_{k+1}(Ω(log 1/ε))`, which is larger, so there is no contradiction.
    - A contradiction needs `|∂T| ≥ f(|T|)` with `f ≫ Ack_k^{-1}` on Følner mass. That is an
      upper bound on Følner tree sizes against `ε`, which is a Følner-function upper bound and is
      not available.
  - *Also checked:* index-graded ratios with `inf f > 2` put every window-full tree with
    `2/λ < |T/10|/|T/01| < λ/2` into `B` (crossing-pair argument). Uniform-by-index grafts cannot
    push measures into that balanced set: the interval-sum ratio `Σ_{[q,s)} w / Σ_{[p,q)} w` is
    unbounded over `p < q < s` for every weight sequence. So this survivor stays undecided, and it
    only concerns `Ack_2`-level constants anyway.
  - *Survivors for `H_k`, `k ≥ 3`:*
    - non-coarsening data, where `∂T` is not dominated by `T` (none is known);
    - coarsening colourings whose interfaces are shown thin by a global argument that is not
      pointwise on inflated trees.
