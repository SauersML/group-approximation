---
rg: 2
id: thompson-f-ore-obstructions-must-see-finite-support-proof
kind: route
title: Order F by the germ at the leftmost support point, embed the group ring into Malcev–Neumann series, and use Guba's lemma for leading monomials
target: thompson-f-ore-obstructions-must-see-finite-support
requires: []
artifacts:
  - research/artifacts/hl-f-p22-invariant-2026-09-13.md
---

`F` is the group of piecewise-linear orientation-preserving homeomorphisms of `[0,1]` with dyadic
breakpoints and slopes in `2^Z`.

**Item 1.** For `g ≠ 1` let `p(g) = inf{t : g(t) ≠ t}`. Then `g` is the identity on `[0, p(g)]`, and on
some `[p(g), p(g) + ε]` it is `t -> p(g) + 2^k (t − p(g))` with `k ≠ 0`; `k = 0` would contradict the
infimum. Put `D(g) = 2^k` and `P = {g ≠ 1 : D(g) > 1}`.
- *`P ⊔ P^-1 = F ∖ {1}`:* `p(g^-1) = p(g)` and `D(g^-1) = 1/D(g)`.
- *`P P ⊆ P`:* let `g, h ∈ P` with `p = min(p(g), p(h))`.
  - If `p(g) < p(h)`, then `h` is the identity near `p`, so `g h = g` near `p`.
  - If `p(h) < p(g)`, then `h(t)` stays in `[0, p(g))` for `t` near `p(h)`, so `g h = h` there.
  - If `p(g) = p(h) = p`, the slopes at `p` multiply.
  In every case `g h ∈ P`.
- *Conjugation invariance:* for `c ∈ F`, `p(c h c^-1) = c(p(h))`. Right derivatives of increasing PL maps
  obey the chain rule, and `h(p) = p`, so
  `D(c h c^-1) = D⁺c(p) · D(h) · D⁺(c^-1)(c(p)) = D(h)`.
So `P` is the positive cone of a bi-invariant order.

**Item 2.** Classical import, not re-read at source: A. I. Malcev (1948) and B. H. Neumann (1949). For a
bi-ordered group `(G, <)` and a field `K`, the functions `G -> K` with well-ordered support form a
division ring under convolution, and it contains `K[G]`. In a division ring `D`, `a·(a^-1 b) = b·1` with
`a^-1 b ≠ 0`. Hence `a D ∩ b D ≠ 0` for all nonzero `a, b`. Any invariant defined on `D` and satisfied
by `a u` and `b v` whenever `a u = b v` in `K[F]` is also satisfied by `u = a^-1 b`, `v = 1` in `D`. So it
can't exclude common multiples unless it uses finiteness of support.

**Item 3.**
- *Products.* For a bi-invariant order, `s < s'` implies `s t < s' t`, and `t < t'` implies `s t < s t'`.
  So among the products `s t` with `s ∈ supp x` and `t ∈ supp y`, the pair of maxima gives the unique
  largest one, with coefficient `x(max) y(max) ≠ 0`. The argument for `min` is symmetric.
- *Common right multiples in `M`.* Guba, arXiv:2305.07113v4, Lemma `gig` (l.615, pinned verbatim in
  `research/artifacts/thompson-f-monomial-doubling-2026-09-13.md` §1): "For any $g_1,...,g_n\in F$ there
  exists $g\in F$ such that $g_1g,\ldots,g_ng\in M$." Given `m_1, m_2 ∈ M`, apply it to `g_1 = m_1^-1 m_2`
  and `g_2 = 1`. That gives `g` with `q := g ∈ M` and `p := m_1^-1 m_2 g ∈ M`, so `m_1 p = m_2 q`.
- *Consequence.* The leading-term equation `max(a) max(u) = max(b) max(v)` forced by `a u = b v` is always
  solvable in `M`, and likewise for `min`. So no leading-term invariant of this order can rule out a
  common multiple.

**Item 4.** This is recorded on main: `dim(aV + bV) < dim aV + dim bV` certifies `aV ∩ bV ≠ 0`, and no
finite count certifies trivial intersection. Graded pieces of `K[M]` are finite-dimensional once letters
are bounded, by the inert-letter-tail step of `thompson-f-p22-explicit-pair-degree-bound-wiedemann-proof`.
So graded arguments are finite counts.

**Trust surface.**
- The Malcev–Neumann theorem.
- Guba's Lemma `gig`, as quoted.
- The standard PL description of `F`.
