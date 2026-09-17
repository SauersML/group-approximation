# Proof attempt for modular-transport-imbalance-is-not-a-strictness-index (held OPEN)

This was the direct-proof route `modular-transport-imbalance-is-not-a-strictness-index-proof`. It was withdrawn from the graph on 2026-09-17 because all three referee lenses refuted the step that candidate 4 (the Jones / Pimsner-Popa index) fails at P1. See `## Attempts` in the claim. Items 1, 2, 3 and 5 were verified by every referee.

Original title: Count orbit sizes on pair types, apply the chain rule, and compute the transport of five tree automata exactly.

Complete direct proof in the artifact.

* **Item 1** (Proposition 1). The type `(a, b)` is a complete invariant of `Gamma`-orbits on pairs, and `K = Gamma_o`
  is transitive on each type class from `o`. The class sizes are `N(a, 0) = 1`, `N(0, b) = 2^b`,
  `N(a, b) = 2^(b-1)`, so `N(a, b) / N(b, a) = 2^(b - a)`. Summing a diagonally invariant `F` over classes gives the
  identity. The same count applies to expectations under any invariant law, which gives the groupoid cocycle.
* **Item 2** (Proposition 2). `x(o)` is a function of `y(D(o))` and independent of `U`. The chain rule along the
  random order of `D(o)` gives `out(o) = log |A_in|`. `t` is diagonally invariant, so item 1 applies.
* **Item 3** (Section 3). Hand derivations of every term. For the product, the independent components transport
  additively. `tree_transport.py` enumerates each `t(u, w)` exactly. It checks that the stated decoder inverts each
  automaton on the whole window (so each automaton is injective), computes `in(o)` at every contributing `u` in the
  radius-3 ball, and asserts `out = log |A_in|` and the weighted identity. The output is `tree_transport.out`.
* **Item 4** (Section 4). The image `tau A^V` misses a cylinder with infinitely many disjoint translates, so it is
  `mu`-null. Given `sigma(y)`, the child pairs are independent and each is uniform on three points. So a cylinder
  fixing `n` pairs has conditional expectation `3^-n` on its consistency event, and no Pimsner-Popa constant is
  positive. A symmetric `f` with `f(a, a) = a` has odd fibres, so it is not balanced when `q` is even. `E f(v) =
  (f(v) + f(v'))/2` is an expectation of index `2` onto `l^inf(V) o p`. Over a group an equivariant site map is a
  right translation, so it is bijective.
* **Item 5** (Section 3). The script verifies the decoder of `kappa`, so `kappa` is injective. `t(u, u) = log q` and
  `t(u, c) = t(u, c') = (1/2) log q`, so the weighted in-mass is `2 log q`. The site law puts mass
  `2q^-2 - q^-3 != q^-2` on `(1, 0)`, so `H(y(o)) < 2 log q`. `kappa` is strict: `z(v) = 0` whenever
  `x0(v) = 1` and `x0(v') = 0`. So the sibling pattern `y(v) = (1, 1)`, `y(v')` with first coordinate `0` never occurs.
