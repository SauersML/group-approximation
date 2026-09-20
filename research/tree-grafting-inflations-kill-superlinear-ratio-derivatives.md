---
rg: 2
id: tree-grafting-inflations-kill-superlinear-ratio-derivatives
kind: claim
title: "Leaf-grafting inflations of the tree F-set kill every coarsening derivative with a superlinear subtree-ratio condition"
distinct_from:
  thompson-f-trees-carry-an-ackermann-derivative-hierarchy: that is the open existence statement H_k; this proves that the natural class of candidates for H_k with k >= 3 (Moore's definition with a superlinear ratio) has a non-thin bad set whenever F is amenable, and gives a test every candidate must pass.
  marginal-derivative-amplification-is-sharp-at-log-height: that bounds the height a derivative datum can certify; this constrains the contraction a derivative datum on the tree F-set can have while keeping a thin bad set.
artifacts:
  - experiments/tree-grafting-inflations-2026-09-17/check_inflation.py
  - experiments/tree-grafting-inflations-2026-09-17/output.txt
---

**ESTABLISHED** by `tree-grafting-inflations-kill-superlinear-ratio-proof` (not yet refereed).

**Setting.** As in `marginal-derivative-amplification-is-sharp-at-log-height`:
- `𝒯` is the set of finite rooted binary trees, with Moore's partial right action of `F`
  (arXiv:0905.1118v7, Sec. 4).
- `Γ = {x0^±1, x1^±1}`.
- `bd(μ) = Σ_{γ∈Γ} Σ_s |μ(s·γ) − μ(s)|`.
- A derivative datum `(∂, A)` satisfies (E′), and `B = 𝒯 ∖ A` is `c`-thin if `μ(B) ≤ c·bd(μ)`.

Trees are sets of leaves, and `T/u` is the subtree of `T` below the node `u`.

**Theorem 1 (Inflation Lemma).** Let `G` act partially on a set `S`, with `Γ` finite and
symmetric. Let `σ : S → S` be *one-sided equivariant*: `σ(s·γ) = σ(s)·γ` whenever `s·γ` is
defined. Then for every finitely supported `μ ≥ 0`:
- `σ_*μ(S) = μ(S)`;
- `bd(σ_*μ) ≤ 2·bd(μ)`.

Injectivity of `σ` is not needed.

**Theorem 2 (grafting inflations).** The following maps `𝒯 → 𝒯` are one-sided equivariant for
the action of `F`. Here `j : ℕ → ℕ` is arbitrary.
- The uniform refinement `σ_j(T) = δ^{j(|T|)}(T)`, where `δ^m(T) = {uw : u ∈ T, w ∈ {0,1}^m}`.
- Grafting a fixed tree `P` at the `k`-th leaf from the left or from the right, and any
  combination of such graftings whose choices depend only on the leaf index and on `|T|`.

**Corollary 3.**
- If a derivative datum on `𝒯` has a `c`-thin bad set `B`, then for every weighted `ε`-Følner
  `μ` and every `σ` as in Theorem 2, `σ_*μ(B) ≤ 2cε·μ(𝒯)`.
- In particular, if `B ⊇ σ(𝒯)` for one such `σ`, then `𝒯` is `2c`-thin, and `F` is
  non-amenable by Moore's Lemma 4.2 (`\label{Folner->trees}`).

**Theorem 4 (class kill).** Consider the following class of data.
- `φ : ℕ_{≥1} → ℕ` is nondecreasing, with `φ(x) ≥ 2x` and `sup_x φ(x)/x = ∞`.
- `(∂, A)` is a derivative datum on `𝒯` such that, for every `T ∈ A`, the tree `∂T` is
  dominated by `T`.
- Call the leaves of `∂T` other than its minimum and maximum its *interior* leaves. Then either
  `|T/v| ≥ φ(|T/u|)` for all consecutive interior leaves `u <_lex v` of `∂T`, or
  `|T/u| ≥ φ(|T/v|)` for all of them.

Put `j(n) = min{ j ≥ 3 : φ(2^{j−3}) > 2^j·n }`, which is finite and nondecreasing. Then the bad
set satisfies `B ⊇ σ_j(𝒯)`. Hence `B` is thin only if `F` is non-amenable. In that case `𝒯`
itself is thin, and `H_k` holds vacuously with `A = ∅`.

Every such datum dies. This includes Moore's Definition 5.1 with `2|T/u| ≤ |T/v|` replaced by
`φ(|T/u|) ≤ |T/v|`. There, `∂T` is trivial on all of `σ_j(𝒯)`, and (E′) fails there.

**Sharpness.** At linear `φ(x) = 2x` the class contains Moore's own datum. Its bad set is
marginal (his lemma `\label{proper_act}`), hence thin by Lemma 3.10 as recorded in `marginal-derivative-amplification-is-sharp-at-log-height`. So the threshold between surviving and dying is exactly
`sup φ(x)/x < ∞`. It follows that a ratio condition on consecutive subtrees can certify at most
exponential (`Ack_2`) contraction without being vacuous.

**Invariant and dying step.**
- *Invariant:* under `δ^j`, the ratio of the sizes of any two subtrees at depth `≤ 3` stays at
  most `8|T|`, while all absolute sizes grow like `2^j`. So a superlinear ratio test fails at the
  crossing pair (last leaf under `01`, first leaf under `10`). That pair is forced to be interior
  by (E′) for `x0` and `x1`.
- *Dying step:* thinness of the bad set. The bad set contains an equivariant copy of `𝒯`, and
  the Inflation Lemma pushes any Følner mass onto it at a cost of a factor 2.
- This turns the super-doubling heuristic (Attempts on
  `thompson-f-trees-carry-an-ackermann-derivative-hierarchy`) into a theorem, and it does so
  without Moore's marginality machinery.

**Necessary condition for any `H_k` candidate.** Every datum with a thin bad set must keep, for
every grafting inflation `σ` and every weighted `ε`-Følner `μ`, at least a fraction
`1 − 2cε` of `σ_*μ` in its good set `A`. So the good set must be essentially closed under
refinement. The conditions that pass this uniform test are:
- scale-invariant conditions, such as Moore's linear ratio;
- *index-graded* ratios `|T/u_{i+1}| ≥ f(i)·|T/u_i|` with `f → ∞` (not decided by this test).
  The crossing pair has ratio `< 8n`, but its index `i` is not bounded, because `U` may place up
  to `log_2|T|` leaves before it, and `f(i) ≤ 8n` is then not forced;
- conditions on height differences, since `δ^j` shifts all heights by `j`.

These survivors are recorded as directions on the open claim.

**Computation.** `check_inflation.py` confirms, on all trees with `≤ 6` leaves:
- equivariance of `δ^{j(n)}`, including a non-monotone `j`, and of a cherry grafting;
- `bd(σ_*μ) ≤ 2bd(μ)` on 300 random measures (worst ratio 1.61);
- for `φ = max(2x, x²)` and `n ≤ 5`, that no `U` exists on `δ^{j(n)}T` in either direction.

**Scope.**
- Unconditional.
- It kills a class of candidates for `H_3` and above, and leaves `H_k` itself open.
- Moore's statements are quoted verbatim in the route.
