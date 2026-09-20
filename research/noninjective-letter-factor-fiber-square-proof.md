---
rg: 2
id: noninjective-letter-factor-fiber-square-proof
kind: route
title: Square the lift over its base, then apply the tied-fiber theorem to the square as a lift of the original injective automaton
target: noninjective-letter-factors-force-squared-fiber-sizes
requires:
  - collapse-lifts-with-tied-largest-fibers-are-surjective
  - ec-groups-share-the-nonsurjunctive-alphabet-sizes
---

This is the complete proof, with notation as in the target. Automata act by `(σx)(g) = f(x|_{gM})`, with a
finite memory `M` that serves `Φ`, `Φ_1` and `Φ_2`. Configurations in `C^G` are written as pairs `(u, v)` with
`u, v ∈ B^G` and `r u = r v` sitewise.

**Step 1: `Ψ` is an injective automaton on the full shift `C^G`.** Let `φ` be the local rule of `Φ`. Put
`Ψ(u, v)(g) = (φ(u|_{gM}), φ(v|_{gM}))`. This depends only on `(u, v)|_{gM}` and commutes with `G`. Its value
lies in `C`, because `r(Φu)(g) = (τ r u)(g) = (τ r v)(g) = r(Φv)(g)`, using `r ∘ Φ = τ ∘ r` and `r u = r v`.
So `Ψ` is a cellular automaton on `C^G`, with `|C| = Σ_a q_a^2`. Injectivity of `Φ` makes `Ψ` injective.

**Step 2: `Ψ` is not onto when `τ` is not injective or `Φ` is not onto.**
- **`τ` not injective.** Pick `x ≠ x'` in `A^G` with `τ x = τ x'`. Since each fiber is nonempty, pick sitewise
  lifts `u` of `x` and `v` of `x'`, so `r u = x` and `r v = x'`. Then `r Φu = τ x = τ x' = r Φv`, so
  `(Φu, Φv) ∈ C^G`. Suppose `(Φu, Φv) = Ψ(u', v')` with `(u', v') ∈ C^G`. Injectivity of `Φ` gives `u' = u`
  and `v' = v`, hence `x = r u' = r v' = x'`, a contradiction.
- **`Φ` not onto.** Pick `u ∉ Φ(B^G)`. Then `(u, u) ∈ C^G` is not in the image, since its first coordinate
  would lie in `Φ(B^G)`.

In both cases `Ψ` is strict, so `Σ_a q_a^2 ∈ NS(G)`. This proves item 1.

**Step 3: `Ψ` is a lift of `Φ` through a letter collapse.** Let `π : C -> B`, `(b, b') -> b`. It is onto,
since `(b, b) ∈ C`. Sitewise `π ∘ Ψ = Φ ∘ π`. The fiber over `b` is `{b} × Q_{r b}`, of size `q_{r b}`. The
largest fiber size of `π` is therefore `q`. The set of letters with largest fibers is
`Z' = r^{-1}{a : q_a = q}`, and `|Z'| = qm`. If `q = 1`, then `r` is a bijection and `τ` is conjugate to `Φ`,
hence injective. So in item 2 we have `q >= 2`, which is what the imported theorem assumes.

**Step 4: item 2.** Apply `collapse-lifts-with-tied-largest-fibers-are-surjective` to `π : C -> B`, the
injective base `Φ` on `B^G`, and the injective lift `Ψ` on `C^G`. That theorem assumes only that `G` is a
group, that `π` is a surjection of finite alphabets with largest fiber size at least `2`, and that base and
lift are injective automata with `π ∘ Ψ = Φ ∘ π`. Its conclusion is that one of `q`, `|Z'|`, `q|Z'|` lies in
`NS(G)`, or `Ψ` and `Φ` are both surjective. By Step 2, `Ψ` is not surjective when `τ` is not injective. So
one of `q`, `qm`, `q^2 m` lies in `NS(G)`.

**Step 5: item 3.**
- If `τ` is not injective, use Step 4.
- If `τ` is injective and `q >= 2`, the imported theorem applies to `(r, τ, Φ)` itself. So one of `q`, `m`,
  `qm` fails, or `Φ` and `τ` are both onto. In the second case both are bijective.
- If `q = 1`, then `τ` is conjugate to `Φ`. Either both are bijective, or `Φ` is strict and
  `|B| = |A| = m = qm` lies in `NS(G)`.

**Step 6: item 4.** Let `r_i : B_i -> A` be the two collapses and put
`C_{12} = {(b_1, b_2) : r_1 b_1 = r_2 b_2}`, which has `Σ_a q_a c_a` letters. Then
`Ψ_{12} = Φ_1 × Φ_2` is an injective automaton on `C_{12}^G`, exactly as in Step 1.
- **`Φ_1` not onto.** Take `u_1 ∉ Φ_1(B_1^G)` and any sitewise lift `u_2` of `r_1 u_1` through `r_2`. Then
  `(u_1, u_2)` is not in the image.
- **`τ` not injective.** Take `x ≠ x'` with `τ x = τ x'`, a lift `u_1` of `x` through `r_1` and a lift `u_2`
  of `x'` through `r_2`. Then `(Φ_1 u_1, Φ_2 u_2)` lies in `C_{12}^G`. Its only candidate preimage is
  `(u_1, u_2)`, which is not in `C_{12}^G`.

**Consequences.**
- For the profile `(2, 1, …, 1)`: `q = 2` and `m = 1`, so the sizes are `2`, `1`, `2` and `4`. The size `1`
  never lies in `NS(G)`. `NS(G)` is closed under multiples by `ec-groups-share-the-nonsurjunctive-alphabet-sizes`,
  so `2 ∈ NS(G)` implies `4 ∈ NS(G)`. Hence item 3 reads: bijective, or `4 ∈ NS(G)`.
- The minimal-size consequence follows from item 3 and the strictness of `Φ`. For a non-uniform profile
  `q < |B|`, `m < |B|` and `qm < |B|`.
- For the surjunctive-group consequence, note that no size lies in `NS(G)`, and apply item 3.
