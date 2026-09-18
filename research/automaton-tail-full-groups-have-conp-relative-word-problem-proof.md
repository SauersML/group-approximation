---
rg: 2
id: automaton-tail-full-groups-have-conp-relative-word-problem-proof
kind: route
title: Guess a cylinder of depth linear in the word length, push it through the tables keeping prefixes long, and test the final prefixes and tail words
target: automaton-tail-full-groups-have-conp-relative-word-problem
requires: []
---

Notation as in `automaton-tail-full-groups-have-conp-relative-word-problem`. For
`g ∈ Aut(X^*)` and a word `v`, `g(v x) = g(v) g|_v(x)`, and
`(gh)|_v = g|_{h(v)} h|_v`.

**0. `FV` is a group, and sections do not grow.**
- *Inverses.* The inverse of (T) is `(u'_{j,i} y_i)_i ↦ (u_{j,i} h_{j,i}^{-1}(y_i))_i`
  on the image rectangles, which partition `Ω` because `f` is a bijection.
- *Composition.* This follows from step 1 below, applied to two elements.
- *Sections.* Because `S_i` is symmetric and closed under sections, for an
  `S_i`-word `h = s_1 ⋯ s_k` and any `v`, the section
  `h|_v = s_1|_{v_1} ⋯ s_k|_{v_k}` is an `(S_i ∪ {1})`-word of length at most `k`.
  Also `h(v)` and `h|_v` are computable in time `O(k·|v|)`.

**1. Pushing a cylinder through a word.** Fix a finite generating set `F` of `Γ`,
closed under inverses, with a table for each element. Let `D >= 1` bound the lengths
of all words `u, u'` in these tables, and `L` the `S_i`-lengths of all their tail maps.
Let `w = f_m ⋯ f_1` with `f_k ∈ F`. Fix `γ = (γ_i)_i` with `|γ_i| = Dm` and write
points of the rectangle `R_γ = ∏[γ_i]` as `(γ_i x_i)_i`.

*Claim.* For `k = 0, …, m` there are words `β_i^{(k)}` with
`|β_i^{(k)}| >= D(m-k)`, and `S_i`-words `h_i^{(k)}` of length at most `Lk`, such that

```text
f_k ⋯ f_1 ( (γ_i x_i)_i ) = ( β_i^{(k)} h_i^{(k)}(x_i) )_i   for all x_i.            (P)
```

They are computable from `γ` and `w` in time polynomial in `m`.

*Proof by induction.*
- *Base.* `k = 0`: `β^{(0)} = γ` and `h^{(0)} = 1`.
- *Choosing the rectangle.* For `k < m`, `|β_i^{(k)}| >= D`. So exactly one rectangle
  `∏[u_i]` of the table of `f_{k+1}` has every `u_i` a prefix of `β_i^{(k)}`. It
  exists because the rectangles partition `Ω` and all `|u_i| <= D`. It is unique
  because they are disjoint.
- *The update.* Write `β_i^{(k)} = u_i μ_i`, and let `u'_i, g_i` be that row's data.
  By (T),
  `f_{k+1}(β_i^{(k)} h_i^{(k)}(x_i)) = u'_i g_i(μ_i) · (g_i|_{μ_i} h_i^{(k)})(x_i)`.
  So put `β_i^{(k+1)} = u'_i g_i(μ_i)` and `h_i^{(k+1)} = g_i|_{μ_i} h_i^{(k)}`.
- *The bounds.* `|β_i^{(k+1)}| = |u'_i| + |β_i^{(k)}| - |u_i| >= D(m-k) - D`, and the
  length of `h_i^{(k+1)}` is at most `L + Lk` by step 0.
- *The cost.* Each step is polynomial in `m`.

**2. When a rectangle is fixed.** By (P) with `k = m`, `w` acts on `R_γ` as
`x_i ↦ β_i h_i(x_i)` in each coordinate. This is the identity of `R_γ` if and only if,
for every `i`, `β_i = γ_i` and `h_i = 1` in `H_i`.
- *If.* This is clear.
- *Only if, case `|β_i| > |γ_i|`.* Then `β_i = γ_i ν` with `ν` nonempty, and every
  `x_i` would equal `ν h_i(x_i)`. That fails for any `x_i` not beginning with `ν`,
  using `|X_i| >= 2`.
- *Only if, case `|β_i| < |γ_i|`.* Then `γ_i = β_i ν`, and `h_i(x_i) = ν x_i` for all
  `x_i`, contradicting surjectivity of `h_i`.
- *Only if, case of equal length.* Then `β_i = γ_i`, and `h_i` fixes `X_i^N`
  pointwise, so `h_i = 1`, because `H_i` acts faithfully on `X_i^*` and hence on its
  boundary.

**3. Item 1.** The rectangles `R_γ` with `|γ_i| = Dm` cover `Ω`. So `w != 1` iff some
`R_γ` is not fixed pointwise. The machine:
1. guesses `γ`, which has size `n·Dm`;
2. computes `(β_i, h_i)` by step 1;
3. accepts if some `β_i != γ_i`, or if the oracle reports some `h_i != 1` in `H_i`.

It runs in polynomial time and accepts exactly the nontrivial `w`. A different finite
generating set changes word lengths only linearly.

**4. Item 2.**
- *First bound.* `NP^P = NP`, so the first bound follows from item 1.
- *Automaton groups are in `PSPACE`.* Let `h = s_1 ⋯ s_k` be an `S`-word. Reading an
  input letter by letter, the composite is a synchronous transducer whose state is
  the vector of current states, at most `|S|^k` vectors. If `h != 1`, some input
  word `v` has `h(v) != v`. A shortest such `v` visits no state vector twice before
  its last letter, so it has length at most `|S|^k`. Guessing `v` letter by letter
  while storing the vector and a counter up to `|S|^k` takes space `O(k)`. So
  nontriviality is in `NPSPACE = PSPACE` (Savitch), and so is `WP(H, S)`.
- *Second bound.* `coNP^{PSPACE} = PSPACE`.

**5. Item 3.**
- *The odometer.* `τ(0w) = 1w`, `τ(1w) = 0τ(w)` has state set `{τ^{±1}, 1}`, closed
  under sections. `<τ> ≅ Z`, whose word problem is in `P`.
- *`G_N` is finite-state.* `N` is odd. Write `x = d + 2x'` with `d ∈ {0,1}`. For
  `x ↦ ax + b` with `a` a 2-adic unit and `a, b ∈ Z[1/N]`, the first output digit is
  `r = (ad + b) mod 2`. The section is `x' ↦ a x' + b'` with `b' = (ad + b - r)/2`.
  The multiplier is unchanged, the denominator of `b'` divides that of `b`, and
  `|b'| <= (|a| + |b| + 1)/2`. So `|b'|` stays bounded along iterated sections, and
  each generator has finitely many states. The union of these states is a finite
  generating set closed under sections.
- *Word problem of `G_N`.* `G_N <= GL_2(Q)` is linear. Entries of a product of `m`
  generator matrices have `O(m)` bits, so its word problem is in `P`.
- *Upper bound.* By item 2, the word problems of `2V_τ` and `2V_{G_N}` are in `coNP`.
  Both are finitely generated. `2V_τ` is of type `F_∞`. `2V_{G_N}` is of type `F_n`
  whenever `G_N` is, by the host nodes, and `G_N` is generated by `x ↦ x + 1` and the
  dilations by the primes `p | N`.
- *Lower bound.* They contain `2V`, a finitely generated subgroup whose word problem
  is coNP-hard (Birget). Length-linear substitution transfers the hardness.

**6. Item 4.** `V_d(G)` is `FV(G)` with `n = 1`. This is the definition in
`rover-nekrashevych-word-problem-reduces-to-self-similar-group`, whose normal form is
(T). If `G` is rational, the states of a finite generating set form a finite symmetric
section-closed generating set. Item 1 applies to every finitely generated subgroup,
including `[V_d(G), V_d(G)]`, which has finite index in the Zaremsky corollary
setting. For linear `G`, such as `BS(1,n)`, `WP(G) ∈ P`, which gives `coNP`. `∎`
