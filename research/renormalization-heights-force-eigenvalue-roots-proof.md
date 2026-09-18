---
rg: 2
id: renormalization-heights-force-eigenvalue-roots-proof
kind: route
title: Restrict eigenfunctions to the tower base and extend them back; compare the two clocks on the minimal base map
target: renormalization-heights-force-eigenvalue-roots
requires: []
---

**Item 1.**
- *(⊆)* Let `f ∘ T = μ f` with `|f| = 1`. On `A`, `f(T^m a) = μ^m f(a)`, so `μ^m ∈ E(T^m|_A)`.
  The map `φ` conjugates `T^m|_A` to `T`, so `f' = f ∘ φ^{-1}` satisfies
  `f'(T x) = f(φ^{-1} T x) = f(T^m φ^{-1} x) = μ^m f'(x)`. So `μ^m ∈ E(T)`.
- *(⊇)* Let `μ^m = ν ∈ E(T)`, with `g ∘ T = ν g`. Then `h = g ∘ φ` satisfies
  `h(T^m a) = g(T φ(a)) = ν h(a)` on `A`. Define `f` on `X` by `f(T^i a) = μ^i h(a)` for
  `a ∈ A`, `0 <= i < m`. This is well defined and continuous: the sets `T^i A` are disjoint and
  clopen, and the maps `T^i` are homeomorphisms.
  - For `i < m-1`, `f(T · T^i a) = μ^{i+1} h(a) = μ f(T^i a)`.
  - For `i = m-1`, `f(T · T^{m-1} a) = f(T^m a) = h(T^m a) = ν h(a) = μ^m h(a) = μ f(T^{m-1} a)`.

  So `μ ∈ E(T)`.
- *(Roots of unity)* Applying `(⊇)` repeatedly to `1 ∈ E(T)` puts every `m^j`-th root of unity in
  `E(T)`. ∎

**Item 2.** Apply item 1 for each `m ∈ M`. If `M` contains every prime, `E(T)` contains every
`p^j`-th root of unity for every prime `p`. It is a group, so it contains every root of unity.

Now let `T` be minimal.
- For each `n`, pick `f_n` with `f_n ∘ T = e^{2πi/n} f_n`. Then `f_n^n` is continuous and
  `T`-invariant, so it is constant. Rescale `f_n` so that `f_n^n = 1`. Then `f_n` takes values
  in the `n`-th roots of unity, and reading it as a map `X -> Z/n` gives `f_n ∘ T = f_n + 1`.
- For `n | N`, both `f_N^{N/n}` and `f_n` are eigenfunctions for `e^{2πi/n}` with values in the
  `n`-th roots of unity. By minimality they differ by a constant `n`-th root of unity. Fixing
  the `f_{j!}` in turn along `j = 1, 2, 3, …` therefore makes them compatible.
- The inverse limit of the maps `X -> Z/j!` is a continuous map `X -> Ẑ` intertwining `T` with
  `+1`. Its image is closed, nonempty and `+1`-invariant, and `+1` is minimal on `Ẑ`, so it is
  surjective. ∎

**Item 3.** Put `F = π ∘ φ_q` on `A_q`. Then `F(T^q a) = π(T φ_q a) = F(a) + g`. Also
`π(T^q a) = π(a) + q g`. Since `G` is uniquely `q`-divisible, `q^{-1}` is a continuous
automorphism of `G`, and `H = F - q^{-1} π` satisfies `H(T^q a) = H(a) + g - q^{-1} q g = H(a)`.
- `T^q|_{A_q}` is conjugate to `T` by `φ_q`, so it is minimal.
- `H` is continuous and `T^q|_{A_q}`-invariant, so it is constant, say `c`.

So `π ∘ φ_q = q^{-1} π + c`. ∎
