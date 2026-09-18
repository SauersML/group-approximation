---
rg: 2
id: odometer-2v-is-fp-simple-and-contains-bs12-proof
kind: route
title: Li's Zappa-Szep finiteness theorem for the odometer on the product 2-graph, Matui's simplicity theorem after a perfectness count, and the baker map as conjugator
target: odometer-2v-is-fp-simple-and-contains-bs12
requires:
  - rationals-embed-in-brin-thompson-group-2v
  - bs12-embeds-in-brin-thompson-2v
  - three-v-contains-aperiodic-rationals
---

Notation is that of the claim. Paths of `Λ` are pairs `μ = (p, w)` of binary words, of degree `(|p|, |w|)`, with
cylinder `μX = C(p) × C(w)`. The source statements are quoted, with line numbers, in
`research/artifacts/gq-affq-kep-odometer-host.md` §1.

**A. The action, pseudo-freeness, condition (F).**
- For a colour-1 word `p` of length `j` with binary value `b`, `a^n·p` is the length-`j` word of `b + n mod 2^j`.
  The restriction is `a^{⌊(b+n)/2^j⌋}`.
- Colour-2 words are fixed, with restriction `a^n`.
- Colour-1 and colour-2 letters commute in `Λ`, and the two recipes agree on both factorizations of a path. So this
  is a degree-preserving self-similar action, and on `X` it is `a^n = τ^n × id`.
- *Pseudo-free:* `a^n` fixes `μ = (p, w)` iff `2^{|p|} | n`, and then its restriction is `a^{n/2^{|p|}}`. So `μ` is
  strongly fixed only if `n = 0`.
- *Right cancellation:* in `D = Λ ⋈ Z`, suppose `(λ,g)(μ,h) = (λ',g')(μ,h)`. Then `λ = λ'`, `g·μ = g'·μ` and
  `g|_μ = g'|_μ`. So `g^{-1}g'` strongly fixes `μ`, and `g = g'`.
- `D` is therefore right cancellative, and (F) holds (Li l.1456).

**B. The groupoid and the normal form.**
- *Basic bisections.* For paths `λ, μ` and `n ∈ Z`, let `Z(λ,n,μ)` be the germs of `μ y ↦ λ (a^n·y)`, with source
  `μX` and range `λX`. Every element of `I_l(D)` acts on `X` locally in this form: `Λ` has lcms, since
  `(p,w)Λ ∩ (p',w')Λ` is empty or a single cylinder. So compact open bisections are finite unions of basic ones.
- *Fixed sets.* Suppose `μ y ↦ λ (a^n·y)` is the identity on a cylinder `μνX`. Comparing the paths `μνz` and
  `λ (a^n·ν)(a^n|_ν·z)` for all `z` forces three things:
  - `d(λ) = d(μ)`, since otherwise a fixed prefix would have to absorb a shifted copy of `z`;
  - `a^n·ν = ν` and `a^n|_ν = 1`, so by pseudo-freeness `n = 0`;
  - `λ = μ`, by unique factorization.

  So only units act trivially on open sets. The groupoid is effective, `F(I_l(D) ⋉ X)` acts faithfully on `X`,
  and it is the group of global finite unions of basic bisections. That is the concrete description in the claim.
- *Hausdorff.* The unit-germ set of `Z(λ,n,μ)` is `μX` if `λ = μ` and `n = 0`, and empty otherwise.
  - If `d(λ) = d(μ)` but `(λ,n) ≠ (μ,0)`, the fixed set is empty: `τ^n × id` has no fixed points for `n ≠ 0`.
  - If `d(λ) ≠ d(μ)`, the fixed set lies in `{x : some coordinate of x is eventually periodic}`, which has empty
    interior.

  Every unit-germ set is therefore clopen, so the groupoid of germs is Hausdorff.
- *Essentially principal.* Points with nontrivial isotropy have an eventually periodic coordinate. They form a
  countable union of nowhere dense sets, so points with trivial isotropy are dense. Together with effectiveness,
  this is Matui's standing assumption (l.1183). The unit space `X` is a Cantor set.
- *Normal form.* An element `f` sends `μ_i y ↦ λ_i (a^{n_i}·y)` on a partition `{μ_i X}`. Let `σ_μ` be the
  homeomorphism `μ y ↦ μ (a·y)` on `μX`, identity elsewhere. Then `f = h ∏_i σ_{μ_i}^{n_i}`, where the `σ`s have
  disjoint supports and `h(μ_i y) = λ_i y` is an element of Brin's `2V` (rectangle prefix replacements). So
  `F = ⟨2V, σ_μ⟩`.

**C. Finiteness.** Apply Li, Example ex:ZS (III) (l.2371–2380), with `C = Λ`, `P = Z_{≥0}^2`, `G = Z`,
`X = Ω_∞`.
- `Λ` is a finite higher-rank graph with two edges of each colour at its vertex, so it meets the assumptions of
  Theorem thm:k-graphs (l.2124).
- The action is degree-preserving (step A).
- (F) holds (step A).
- `D^*(w,w) = St(Z, v) = Z` (rem:ZS-Stab, `Λ^* = Λ^0`), which is of type `F_∞`.

Take `𝔢_P = ∅`, so the reduction is to `Y = X`: by Li l.1178, `X(v; 𝔢)` shrinks as `𝔢` grows, so
`X(v; ∅) = vX = X`. Hence `2V_τ` is of type `F_n` for every `n`, that is, of type `F_∞`.

**D. `2V_τ = ⟨2V, s⟩`, perfectness, simplicity.**
- *Generation.*
  - `s = σ_∅`.
  - With `q ∈ 2V` the colour-1 first-digit swap `q(jx, y) = ((1-j)x, y)`: `q s (0x, y) = q(1x, y) = (0x, y)` and
    `q s (1x, y) = q(0τx, y) = (1τx, y)`, so `qs = σ_{(1,∅)}`.
  - For proper cylinders `μX ≠ X ≠ μ'X`, some `h ∈ 2V` acts on `μX` as the single prefix replacement `μ ↦ μ'`
    and maps `X ∖ μX` onto `X ∖ μ'X`, since nonempty rectangle unions can be split to equal numbers of
    rectangles. Then `h σ_μ h^{-1} = σ_{μ'}`.
  - So every `σ_μ` lies in `⟨2V, s⟩`, and `F = ⟨2V, s⟩`.
- *Perfect.* Let `c` be the common image of the proper `σ_μ` in `F_ab`. Splitting by the first colour-2 letter,
  on which `a` acts trivially with restriction `a`, gives `σ_{(1,∅)} = σ_{(1,0)} σ_{(1,1)}`, so `c = 2c` and `c = 0`.
  `2V` is simple (Brin), so its image in `F_ab` is `0`. Hence `F_ab = 0`.
- *Minimal:* `2V ⊆ F` already acts minimally on `X`.
- *Purely infinite:* a clopen `A` is a finite disjoint union of cylinders `μX`. The bisections
  `U = ∪ {μ y ↦ μ(ε,0) y}` and `V = ∪ {μ y ↦ μ(ε,1) y}`, where `(ε,j)` is the colour-2 letter `j`, have
  `s(U) = s(V) = A`, disjoint ranges, and ranges inside `A` (Matui, Def. pi).
- By Matui Theorem simple2, `D(F)` is simple. Since `F = D(F)`, `F` is simple.

**E. `BS(1,2)`.** `u(x, y_0y) = (y_0x, y)` maps the rectangles `C × C(j)` onto `C(j) × C` by prefix replacement,
so `u ∈ 2V`, and `u^{-1}(x_0x', y) = (x', x_0y)`. Then
`u s u^{-1}(x_0x', y) = u(τx', x_0y) = (x_0 τx', y) = (τ^2(x_0x'), y) = s^2(x_0x', y)`,
since `τ^2(jw) = jτ(w)`. `s` has infinite order. The hand check of `bs12-embeds-in-brin-thompson-2v` (every
proper quotient of `BS(1,2)` kills a power of the generator) gives `⟨s,u⟩ ≅ BS(1,2)`. ∎ (items 1–4)

**F. `Q`.** `2V ≤ 2V_τ` and `rationals-embed-in-brin-thompson-group-2v` give `(Q,+) ≤ 2V_τ`. For `Q_τ`: the pieces
`(x, y_jw) ↦ (τ^q x, y'_jw)` (`q ∈ {0,1}`) of the mixed-radix elements `s_n`, run with base `τ` in place of `t`, are
basic bisections (`p = p' = ∅`, `n = q`). So each `s_n ∈ 2V_τ`. The relations `s_n^{n+1} = s_{n-1}` and the
injectivity use only the counter arithmetic and the infinite order of the base, exactly as in
`three-v-contains-aperiodic-rationals-proof`. So `Q_τ = ∪⟨s_n⟩ ≅ Q`.
- `s_1(x, 0w) = (x, 1w)` and `s_1(x, 1w) = (τx, 0w)`.
- From E, `u^{-1}su(x, 0y) = u^{-1}(τ(0x), y) = u^{-1}(1x, y) = (x, 1y)` and
  `u^{-1}su(x, 1y) = u^{-1}(τ(1x), y) = u^{-1}(0τx, y) = (τx, 0y)`.
- So `s_1 = u^{-1}su`. ∎ (item 5)
