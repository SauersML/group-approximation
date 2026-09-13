---
rg: 2
id: bernoulli-isomorphism-from-approximate-right-inverses-proof
kind: route
title: Approximate right inverses put each factor-joining set in the closure of the other, and the category theorem in their common closure yields isomorphism joinings
target: bernoulli-isomorphism-from-approximate-right-inverses
requires:
  - iid-density-iff-collapse-and-endomorphism-density
  - iid-generators-not-dense-at-positive-rokhlin-supremum
  - nonamenable-bernoulli-shifts-are-weakly-isomorphic
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
---

Notation of the target. A **window event** on `L^G × K^G` is a set depending only on the coordinates in a finite
`W ⊆ G` in each factor. Window events are clopen, and they determine the weak* topology on `J`.

**Lemma (second coordinates close).** Let `a: X → L^G` and `b, b': X → K^G` be measurable maps on a probability
space `(X, µ)`. Suppose `b, b'` are equivariant, `µ` is invariant, and `µ{b(x)(1) ≠ b'(x)(1)} = ε`. Then for every
window event `E` with window `W`, `|µ{(a, b) ∈ E} − µ{(a, b') ∈ E}| <= |W|·ε`. Indeed `b(x)(g) = b(g^-1 x)(1)`, so
`b` and `b'` differ on the coordinates in `W` on a set of measure at most `|W|·ε`.

**Item 1.**
- (⇒) Let `ζ_n ∈ End_G(X_λ)` with `ε_n = d(φ ∘ ζ_n, id) → 0`. Apply the lemma to `a = ζ_n`, `b = id`, `b' = φ ∘ ζ_n`.
  Then `law(ζ_n(x), x)` is within `|W|·ε_n` of `law(ζ_n(x), φ(ζ_n(x)))` on window events. The latter law is
  `graph(φ)`, because `ζ_n(x)` has law `λ^G`. So the transposed graphs of `ζ_n` converge to `graph(φ)`.
- (⇐) Suppose `law(ζ_n(x), x) → graph(φ)`, and fix `ε > 0`.
  - Choose a finite `W` and `f: L^W → L` with `λ^G{y : φ(y)(1) ≠ f(y|W)} < ε`.
  - The window event `E = {(a, b) : b(1) ≠ f(a|W)}` has `graph(φ)(E) < ε`. So for large `n`,
    `µ{x : x(1) ≠ f(ζ_n(x)|W)} < 2ε`.
  - Since `ζ_n(x)` has law `λ^G`, `µ{f(ζ_n(x)|W) ≠ φ(ζ_n(x))(1)} < ε`.

  Hence `d(φ ∘ ζ_n, id) < 3ε`.
- *Transposition.* By (⇒), graphs lie in the closure of transposed graphs. Transposition is a homeomorphism of
  `J(X_λ, X_λ)` that exchanges the two sets, so the two closures coincide. Conversely, invariance of the closure gives
  graphs in the closure of transposed graphs, and (⇐) gives ARI.

**Item 2.** Fix `π' ∈ Fac_G(X_κ, X_λ)` and `φ ∈ Fac_G(X_λ, X_κ)`.
- Put `η = φ ∘ π' ∈ End_G(X_κ)`. ARI gives `ζ ∈ End_G(X_κ)` with `d(η ∘ ζ, id) < ε`.
- Put `ψ = π' ∘ ζ ∈ Fac_G(X_κ, X_λ)`. Then `φ ∘ ψ = η ∘ ζ`, so `d(φ ∘ ψ, id) < ε`.
- Apply the lemma to `a = ψ`, `b = id`, `b' = φ ∘ ψ` on `X_κ`. The transposed graph `law(ψ(k), k)` is within `|W|·ε` of
  `law(ψ(k), φ(ψ(k)))` on window events. That law is `graph(φ)`, because `ψ(k)` has law `λ^G`.

**Item 3.**
- *`A` is `G_δ`.* `ν ∈ A` iff the `K`-coordinate at `1_G` is measurable, modulo `ν`, with respect to the
  `L`-coordinates. By martingale convergence this holds iff for every `m >= 1` some finite `W` and
  `F: L^W → K` have `ν{k(1) ≠ F(l|W)} < 1/m`. Each such condition defines an open set, so `A` is a countable
  intersection of countable unions of open sets.
  - If `k(1) = f_1(l)` `ν`-a.e., invariance gives `k(g) = f_1(g^-1·l)`. So `k = f(l)` with `f` equivariant and
    pushing `λ^G` to `κ^G`, and `ν = graph(f)`.
  - The same argument shows `B` is `G_δ`.
- *Both sets sit inside `Y`.* By item 2 applied to `X_κ`, `A ⊆ cl(B)`. By item 2 with the roles exchanged,
  `B ⊆ cl(A)`, after transposing. So `A, B ⊆ Y`.
- *Density and category.* `Y ⊆ cl(A)`, so `A` is dense in `Y`; likewise `B`. `Y` is closed in the compact metrizable
  `J(X_λ, X_κ)`, hence a Baire space. It is non-empty, because `A ≠ ∅`. By the Baire category theorem `A ∩ B` is a
  dense `G_δ` subset of `Y`, in particular non-empty.
- *Isomorphism.* For `ν ∈ A ∩ B`, `k = f(l)` and `l = h(k)` `ν`-a.e. So `h ∘ f = id` `λ^G`-a.e. and `f ∘ h = id`
  `κ^G`-a.e., and `f` is an isomorphism.

**Item 4.** DENSE(`X`) says, for every `φ` and `ε`, some `T ∈ Aut_G(X) ⊆ End_G(X)` has `d(φ ∘ T, id) < ε` (Reading
of `iid-density-iff-collapse-and-endomorphism-density`). That is ARI with `ζ = T`. For the second sentence use item 4,
(a) ⇒ (d), of the same node.

**Item 5.** Let `s = h^Rok_sup(G) > 0` and `H(λ) > 0`.
- Choose a two-point base `(A_0, p)` with `0 < a = H(p) < min(H(λ), s, log 2)`, and any finite base `(B_0, q)` with `H(q) > 0`.
  Put `κ = p × q` on `K = A_0 × B_0`.
- Item 4 of `iid-generators-not-dense-at-positive-rokhlin-supremum` gives some `ν_ξ ∈ J(X_λ, X_κ)` in which the
  `K`-coordinates determine the `L`-coordinates, with a weak* neighbourhood containing no joining in which the
  `L`-coordinates determine the `K`-coordinates. So `ν_ξ ∈ B \ cl(A)`.
- `G` is nonamenable, so `Fac_G(X_λ, X_κ) ≠ ∅` by `nonamenable-bernoulli-shifts-are-weakly-isomorphic`. If `X_λ` had
  ARI, item 2 with the roles of `κ` and `λ` exchanged would give `B ⊆ cl(A)`. That is a contradiction.

**Item 6.** Let `h^Rok_sup(G) = 0` and `H(κ) > 0`.
- By item 1 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, `h^Rok_G(X_κ) = min(H(κ), 0) = 0`.
- By item 4 there, a sofic `G` would give `h^Rok_G(X_κ) = H(κ) > 0`. So `G` is not sofic, hence not amenable.
- By `nonamenable-bernoulli-shifts-are-weakly-isomorphic` there are factor maps in both directions between any two
  finite-base Bernoulli shifts. Item 3 gives the isomorphisms. Two finite bases of different entropy with
  isomorphic shifts put their entropy difference in `D(G) \ {0}`.
