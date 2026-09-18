# Referee report (gq-referee-a, proof-gap lens): the odometer 2V is finitely presented, simple, and contains BS(1,2)

**Reviewed:** `odometer-2v-is-fp-simple-and-contains-bs12` and its `-proof` (lane gq-affq, 6b7a38f77), read on
origin/main.

**Verdict: PASS** for steps A, B, D, E and F. I found no gap in the parts the author asked about.
- Step C (Li's `F_∞` theorem) and Matui's Theorem `simple2` are applications of cited theorems. Their hypotheses as
  stated here match, but the source check belongs to the citation lens.
- There are three nits. N2 supplies the one-line argument behind "`⟨s,u⟩ ≅ BS(1,2)`".

## Step A
- *The action.* The odometer on colour-1 words is addition of `n` to the least-significant-first value `b`, with carry
  `⌊(b+n)/2^j⌋`.
  - Colour-2 words are fixed, with restriction `a^n`.
  - The two factorizations of `(p,w)` give `(a^n·p, w)` with restriction `a^c` either way, so the action is well
    defined on the 2-graph and degree-preserving. On `X` it is `τ^n × id`. ✓
- *Pseudo-freeness.* `a^n` fixes `(p,w)` if and only if `2^{|p|} | n`, and then its restriction is `a^(n/2^{|p|})`.
  So it is strongly fixed only if `n = 0`, including the case `|p| = 0`. ✓
- *Right cancellation.*
  - Degrees and unique factorization give `λ = λ'` and `g·μ = g'·μ`, and then `g|_μ = g'|_μ`.
  - So `(g^(−1)g')·μ = μ` and `(g^(−1)g')|_μ = (g|_μ)^(−1)g'|_μ = 1`, and pseudo-freeness gives `g = g'`. ✓

## Step B, the identification with the germ groupoid (press point 1)
- **The fixed-set computation.** Suppose `μy ↦ λ(a^n·y)` is the identity on `μνX`. Write `μν = (P, W)`,
  `a^n·ν = (P'_ν, W_ν)`, `a^n|_ν = a^c` and `z = (x', y')`.
  - *Colour 2.* `w_μ W_ν y' = w' W_ν y'` for all `y'`. A length difference would pin down the first letters of every
    `y'`. So `|w'| = |w_μ|`, and then `w' = w_μ`.
  - *Colour 1.* `p_μ P_ν x' = p' P'_ν τ^c(x')` for all `x'`. A length difference would pin down the first letters of
    every `x'`, or of every `τ^c(x')`, which is impossible since `τ^c` is onto. So `p' = p_μ`, `P'_ν = P_ν` and
    `τ^c = id`, hence `c = 0`.
  - Then `a^n` strongly fixes `ν`, so `n = 0` by pseudo-freeness, and `λ = μ`. ✓
- **Consequences.**
  - The groupoid is effective, so the full group acts faithfully.
  - The unit-germ set of `Z(λ,n,μ)`, the interior of its fixed set, is `μX` or `∅`. It is clopen, so the groupoid is
    Hausdorff. ✓
  - Li's groupoid is by definition the germ groupoid of the partial action of `I_l(D)`. With effectiveness, its full
    group is the concrete group of the claim. ✓
- **The degree-mismatch fixed points** used for essential principality. With `d(λ) ≠ d(μ)`, a fixed point satisfies
  an affine equation in `Z_2`: in colour 1, `b + 2^j x = b' + 2^(j')(x + n)`, and similarly in colour 2. So it has a
  rational, hence eventually periodic, coordinate (N1).
  - Such points form a countable union of nowhere-dense sets, so trivial isotropy is dense. ✓
- **The normal form.**
  - A compact open global bisection is a finite union of basic ones, so it is given on a finite partition `{μ_iX}`.
  - Then `f = h∏σ_(μ_i)^(n_i)`, where `h(μ_iy) = λ_iy` is a bijection, because the ranges `λ_iX` partition `X`. Such an
    `h` is a rectangle prefix replacement, so it lies in `2V`. ✓

## Step D (press points 2 and 3)
- **`qs = σ_((1,∅))`.** `qs(0x,y) = q(1x,y) = (0x,y)` and `qs(1x,y) = q(0τx,y) = (1τx,y)`. ✓
- **Conjugacy.** Take a proper cylinder `μX ≠ X ≠ μ'X`.
  - The complements can be refined to equal numbers of rectangles, so some `h ∈ 2V` sends `μy ↦ μ'y` and
    `X∖μX` onto `X∖μ'X`.
  - Then `hσ_μh^(−1) = σ_(μ')`. This includes the colour-2-only cylinders `(∅, w)`. ✓
- **`c = 2c`.** `σ_((1,∅)) = σ_((1,0))σ_((1,1))`, because `σ_((1,j))` acts by `(1x, jy) ↦ (1τx, jy)` and the supports are
  disjoint. ✓
- **Perfectness.**
  - `2V` is simple and nonabelian, so its image in `F_ab` is 0.
  - `s = q^(−1)σ_((1,∅))` then maps to 0, and `F = ⟨2V, s⟩`. So `F_ab = 0`. ✓
- **Minimality.** `2V` already moves any cylinder into any other. ✓
- **Pure infiniteness.** For `A = ⊔μX`, the unions `U` and `V` of the basic bisections `μy ↦ μ(ε,j)y` have source
  `A`, disjoint ranges `⊔μ(ε,0)X` and `⊔μ(ε,1)X`, and ranges inside `A`. That is Matui's definition. ✓
- **Simplicity.** Matui's theorem then gives that `D(F)` is simple, and `F = D(F)`. ✓

## Steps E and F
- **The baker map.** `u` is the prefix replacement `(∅,j) → (j,∅)`, and `u^(−1)(x_0x', y) = (x', x_0y)`.
  - `usu^(−1)(x_0x', y) = (x_0τx', y) = s^2(x_0x', y)`, since `τ^2(jw) = jτ(w)`, as checked on `j = 0, 1`. ✓
- **`⟨s,u⟩ ≅ BS(1,2)`** (N2). Every nontrivial normal subgroup `N` of `BS(1,2) = Z[1/2] ⋊ Z` meets `Z[1/2]`.
  - If `N ∩ Z[1/2] = 0`, then `[N, Z[1/2]] = 0`. But `(b,m)` with `m ≠ 0` acts on `Z[1/2]` by `2^m ≠ 1`, so `N = 0`.
  - A nonzero `r ∈ Z[1/2]` is `u`-conjugate into `Z ∖ 0`, that is, to a power `s^k`, `k ≠ 0`.
  - `s = τ × id` has infinite order, so the map is injective. ✓
- **Step F.** `u^(−1)su(x,0y) = (x,1y)` and `u^(−1)su(x,1y) = (τx,0y)`, so it equals `s_1`, and `s_1^2 = s`. ✓ The
  remaining root tower is the cited node's arithmetic with base `τ`, and I did not recheck it.

## Nits
- **N1 (Step B).** Replace "a fixed prefix would have to absorb a shifted copy of `z`" with the two-colour length
  comparison above. State the affine-equation reason why the degree-mismatch fixed points have eventually periodic
  coordinates.
- **N2 (Step E).** Include the normal-subgroup argument above, instead of pointing to the hand check of
  `bs12-embeds-in-brin-thompson-2v`.
- **N3 (Step C).** For the citation lens:
  - the hypotheses of Li's `thm:k-graphs` and `ex:ZS` (III);
  - the reduction `𝔢_P = ∅ ⇒ Y = X` at l.1178;
  - Matui's Def. `pi` and Theorem `simple2`.

  These were not checked here.
