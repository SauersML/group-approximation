# Referee report (gq-referee-a, proof-gap lens): run compression at a commonly fixed letter, and the spine Grigorchuk automaton

**Reviewed** (lane bh-self-similar, ef03b7c34), read on origin/main:
- `commonly-fixed-letters-compress-to-faithful-actions`, with its `-proof`;
- `spine-grigorchuk-automaton-group-has-a-bounded-action`, with the proof inline.

**Verdict: PASS for both.**
- There is one required fix (W1), on how the Boone–Higman conclusion is sourced. The mathematics of both nodes is
  correct.
- There is one nit, on the choice of `p`.

## 1. Run compression
- **`σ` and `σ^b = σ^([b])` (the author asked about this).**
  - `(gh)|_x = g|_(h(x)) h|_x = g|_x h|_x`, because `h(x) = x`, and `σ(S) ⊆ S`.
  - For `p ≥ 1` with `σ^(2p) = σ^p` on `S`, `σ^p` is the identity on `σ^p(S)`, and `σ(σ^p S) = σ^p(σS) ⊆ σ^p S`.
    Since `σ^(p−1)∘σ = id` there, `σ` permutes `σ^p(S)`.
  - So `σ^(p+q) = σ^p` on `S`, hence on `G`, since both are endomorphisms agreeing on generators. Downward induction
    by `q` gives `σ^b = σ^([b])`. ✓
  - For `p = 0` this needs `σ` to permute `S` (N1).
- **The cocycle rule (the author asked about this).**
  - `π_(gh) = π_g π_h` and `(gh)|_(y,c) = g|_(π_h(y,c)) h|_(y,c)` both follow from `σ^c(gh) = σ^c(g)σ^c(h)` and the old
    cocycle rule at `y`.
  - So `g ↦ (π_g; (g|_a))` is a homomorphism `G → G ≀ Sym(A)`, which defines an action on `A^*`.
  - The states are `S`, because `σ^c(s) ∈ S` and sections of states are states. ✓
- **The equivariance of `κ` on `Ω` (the author asked about this).**
  - `g(x^bη) = x^bσ^b(g)(η)`, and `σ^b(g)` maps `Y` to `Y`. So `g` preserves the exact run lengths `b_j` and moves only
    the `Y`-letters. In particular `Ω` is `G`-invariant.
  - The first letter matches: `κ(gξ)` and `g κ(ξ)` both begin with `(σ^([b_0])(g)(y_0), [b_0])`, followed by
    `κ(hξ')` and `h κ(ξ')` respectively, with the same `h = g|_(y_0,[b_0])`.
  - Induction on the letter index, uniformly in `g`, gives `κ(gξ) = gκ(ξ)`.
  - `κ` is onto, via `b_j = c_j`. ✓
- **Faithfulness (the author asked about this).**
  - If `g` is trivial on `A^*`, then `κ(gξ) = κ(ξ)` gives `y_j' = y_j`, and the run lengths agree exactly. So
    `gξ = ξ` on `Ω`.
  - `Ω` is dense, since `Y ≠ ∅`, and `g` is continuous, so `g = 1`. ✓
- **Consequences 1 and 4.**
  - With `σ = id`, the letters `(y,0)` carry exactly the restriction of `G` to `Y^*`.
  - If `|A| = 1`, the tree is a ray, so `G = 1`. ✓

## 2. The spine Grigorchuk automaton
- **The data.**
  - `σ` kills `a, b, c, d` and fixes each `ŝ_γ`. So `σ² = σ` with `p = 1`, `σ = id` on `σ(S)`, and `q = 1`.
  - `A = {0,1} × {0,1}`.
  - On `(y,1)`, `σ(a..d) = 1` acts trivially, and `σ(ŝ_γ) = ŝ_γ` has trivial root permutation, with sections `γ` and `1`.
  - So `ŝ_γ = (γ, 1, γ, 1)`, with no self-loop. ✓
- **Boundedness (the author asked about this).**
  - The sections of `a..d` at the letters `(y,1)` are trivial, and every section of `ŝ_γ` lies in `{1, a, b, c, d}`.
  - So the only cycle through nontrivial states is Grigorchuk's `b → c → d → b` along `(1,0)`, and there are no two
    distinct cycles joined by a path. The automaton is bounded. ✓
- **Contraction.**
  - Every level-one section of `g` is a product of at most `|g|` letter sections from `{1,a,b,c,d}`.
  - `Γ` acts on the `(y,0)`-letters by Grigorchuk's recursion and trivially below the `(y,1)`-letters.
  - So Grigorchuk's contraction and nucleus apply from level 2 on. ✓
- **`V_4` finitely presented.** This is Nekrashevych's contracting theorem, a cited node. ✓

## Required fix
- **W1 (the Boone–Higman step, in both nodes).**
  - The step from "`V_4(G)` finitely presented" to "the relator kernel is a finitely generated lift ideal" is the
    necessity half of Theorem A of `rover-nekrashevych-fp-iff-finite-lift-presentation`. That node is still marked
    unreviewed, and `lift-presented-automaton-groups-satisfy-boone-higman` itself records its consequence 1 as resting on
    it.
  - So as written, consequence 3 of the compression node and the spine node's conclusion are conditional on it.
  - The spine node's own Remark gives an **unconditional** route, which I checked:
    - every element preserves the second coordinate of `A`, and the sections at `(1,1)` are trivial;
    - so `G ↪ (Γ ≀ C_2) × Γ`, acting on the `(y,0)`-subtrees and on the `(0,1)`-subtree;
    - that group embeds in Röver's group `VΓ`, taking `Γ ≀ C_2` on two cones with a swap from `V`, and `Γ` on a third
      cone;
    - `VΓ` is finitely presented and simple (Röver).
  - Make that route the proof of the Boone–Higman clause, or state the conditional. The compression method, which is
    the point of the node, is unaffected.

## Nit
- **N1 (compression, the setting).** `p = 0` is always "idempotent". State the choice as "`σ^p = σ^(p+q)` on `S`
  with `q ≥ 1`", or require `p ≥ 1` unless `σ` permutes `S`. Otherwise `q` is undefined when `σ` is not a permutation
  of `S`.
