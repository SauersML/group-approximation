---
rg: 2
id: toeplitz-enriched-order-seed-is-a-rigid-relative-seed
kind: claim
title: The Toeplitz-enriched order seed Y_E of (BS(1,m), ⟨a⟩) is a rigid relative seed, so (Z_J, F(a)) ∈ 𝓡 unconditionally; rigidity comes from one sign chain, a tree of integrality atoms, and descent of the Toeplitz letters along their zero chains
distinct_from:
  toeplitz-layer-seeds-the-digit-letters-along-a-path-splitting: that builds Y_E, proves (RS1), (DM), (EX) and (M), and glues along the path splitting conditionally on (RS2) and (RS3) of Y_E; this proves (RS2) and (RS3), which removes the condition.
  ordered-orbits-give-rigid-relative-seeds: that is the plain order seed, rigid by one chain; this adds integrality, digit and Toeplitz layers, and shows they commute with the chain and with each other.
---

**ESTABLISHED** by the proof below (lane bh-invent-03, 2026-09-19; elementary lane proof, not reviewed; no priority
claimed). **Checked by bh-invent-14 (2026-09-19): PASS.** Every step of (a)–(d) and of the (RS2)
classification was re-derived, including the telescoping partition in (c) and the offset-±1 pin in (d); no gap
found. Landed by bh-invent-14 on the author's behalf, text unchanged, after gqland's disk floor had blocked the author.
Notation, the letters `σ, L, D, E`, the rules (O), (L), (D), (Tz), (Cut) and (RS1) are those of
`toeplitz-layer-seeds-the-digit-letters-along-a-path-splitting` (afa36f070, bh-invent-14).

We have `V = BS(1,m)` with `m ≥ 2`, `x(t) = t + 1` and `a(t) = t/m`.
- **Positions and scales.** A site `g` has position `pos(g) = g(0)` and scale `s_g`. Also `pos(gx^n) = pos(g) + n s_g`,
  `pos(ga) = pos(g)` and `s_(ga) = s_g/m`.
- **Vertices.** These are the `⟨x⟩`-cosets. The lattice of `v = g⟨x⟩` is `pos(g) + s_g Z`.
- **The tree.** The *parent* of `v` is `ga⟨x⟩` (a finer lattice). Its `m` *children* are the cosets
  `g x^j a^(-1)⟨x⟩` (the coarser lattices). The upward rays converge to one end `ω`.

## Statement

1. **(RS2).** `Y_E` is the orbit closure of its forced point.
2. **(RS3).** `Y_E` is `D`-quantum rigid for every `D ≥ 1` over every field.
3. **Consequence.** With §§1–3 of afa36f070 and `edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy`, the
   pair `(Z_J, F(a)) ∈ 𝓡` holds **unconditionally**. So do the pairs that afa36f070 derives from it: `(Z_J, Σ)`
   through `θ`, and then the J-pairs.

## Proof of (RS3)

Let `(E)` be a `D`-family.
- **Sign letters.** Write `N(y) = E_−` and `Q(y) = E_− + E_*` at position `y`. They are functions of position,
  because (O) is exact along `a`.
- **Integrality.** `Λ_v` is the `L`-letter, the same operator at every site of `v` by exact transport along `x`.
- **Digits.** `Δ^d_g = [D(g) = d]`.
- **Letters at a site** are products of events of the four layers. So it suffices to show that any two layer events
  commute.

**(a) Signs.** (O) contains the order-seed rules. So, as in `ordered-orbits-give-rigid-relative-seeds`, all `N(y)` and
`Q(y)` lie in one chain: `N(y) ≤ Q(y) ≤ N(y')` for `y < y'`.

**(b) Integrality and digits: a tree of atoms.**
- (L) gives `Λ_(g x^j a^(-1)) = Λ_v Δ^j_g`. Since `Σ_d Δ^d_g = Λ_v`, each `Λ_v` is the orthogonal sum of its `m`
  children's.
- (L) also gives `Λ_v ≤ Λ_(parent)`. So `Λ`s of comparable vertices are comparable, and `Λ`s of incomparable
  vertices are orthogonal: they lie under distinct children of their lowest common ancestor.
- So all `Λ_v` commute. The digit events are `Δ^j_g = Λ_(child j)`, so they are `Λ`s too.

**(c) Integrality against signs.** Fix `v`, with lattice points `y_n = p + ns`. Put `G(y_n) = N(y_(n+1)) − Q(y_n)`
("the cut lies strictly between `y_n` and `y_(n+1)`").
- **A partition of unity.** Telescoping gives
  `1 = N(y_(−M)) + Σ_(|n| ≤ M) (Q − N)(y_n) + Σ_(−M ≤ n < M) G(y_n) + (1 − Q(y_M))`.
- **Three facts.**
  - (Cut) gives `Λ_v G(y_n) = 0`.
  - `σ = *` implies `L`, so `E_*(y_n) ≤ Λ_v`.
  - `B := N(y_(−M))` and `T := 1 − Q(y_M)` are sign letters at sites of `v`, so they commute with `Λ_v` (Q1).
- **Hence** `Λ_v = Σ_(|n|≤M) E_*(y_n) + Λ_v B + Λ_v T`.
- **Commutation.** For any position `y`, choose `M` with `y_(−M) < y < y_M`. Then `B ≤ N(y)` and `T N(y) = 0`. So
  `Λ_v N(y) = Σ E_* N(y) + Λ_v B = N(y) Λ_v`. The same holds for `Q(y)`.

**(d) Toeplitz letters: descent.** Take `e ≠ *`; note `[E = *] = E_*` is a sign letter. By (Tz),
`[E(g) = e] = Δ^e_g + [E(ga^(-1)) = e]`, where the second letter lies below `Δ^0_g = Λ_(child 0)`. Iterating,
`[E(g) = e] = Σ_(j<J) Λ_(c_j) + X^(J)`, where:
- the `c_j` are vertices;
- `X^(J) = [E(g a^(-J)) = e]` lies below `Λ_(w_J)`, with `w_J` the vertex of `g a^(-J)` at depth `depth(v) + J`.

The `Λ`-terms commute with everything, by (b) and (c). It remains to treat the remainder `X^(J)` against each layer.
- **Against `Λ_w`.** Take `J` so large that `w_J` is neither `w` nor an ancestor of `w`. Then `Λ_(w_J)` is
  `≤ Λ_w` or orthogonal to it, and `X^(J) ≤ Λ_(w_J)` commutes with `Λ_w`.
- **Against another Toeplitz letter** `[E(h) = e']` with remainder `X'^(K)`. Choose `J, K` with
  `depth(w_J) = depth(w'_K)`. The two vertices are then equal or orthogonal.
  - If they are orthogonal, both products vanish.
  - If they are equal, it remains to show that Toeplitz letters at sites `s` and `s x^n` of one vertex commute. We
    induct on `|n|`:
    - `n = 0`: Q1.
    - `m ∤ n`: `Δ^0_s Δ^0_(sx^n) = 0`, so after expanding both letters one step, every cross term is a product of
      commuting `Λ`s or vanishes.
    - `n = mℓ`: both expand into the same `Δ^0_s` times letters at `s a^(-1)` and `s a^(-1) x^ℓ`, which commute by
      induction, since `|ℓ| < |n|`.
- **Against signs.** Let `p = pos(g)`. Then `g a^(-J)` has position `p` and scale `s m^J`. For fixed `y`, choose `J` with
  `|y − p| < s m^J`, and use (c) at `w_J` with `M = 1`. This gives
  `X^(J) = X^(J) E_*(p − s m^J) + X^(J) E_*(p + s m^J) + X^(J) Λ B_1 + X^(J) Λ T_1`.
  - All factors sit at `g a^(-J)` or at its `x^(±1)`-neighbours, so they commute (Q2). Also `X^(J) E_*(p) = 0`.
  - A `*` at offset `±1` forces `D(g a^(-J)) = ±1 ≠ 0`, hence `E(g a^(-J)) = ±1 mod m` by (D), (Tz). So
    `X^(J) E_*(p ± s m^J)` is `0` or `E_*(p ± s m^J)`, which is in the chain.
  - `X^(J) Λ B_1 ≤ B_1 ≤ N(y)` and `X^(J) Λ T_1 ≤ T_1 ⊥ N(y)`. So both terms commute with `N(y)`, and likewise with
    `Q(y)`.

So all layer events commute, and `Y_E` is rigid. ∎

## Proof of (RS2)

Let `y ∈ Y_E`.
- **A `*` somewhere.** By (O) the sign layer is a cut with at most one `*`. If there is a `*`, the forcing of (RS1)
  makes `y` a translate.
- **The integral set.** Otherwise let `I` be the set of integral vertices. By (b), `I` is up-closed and each integral
  vertex has exactly one integral child. So `I` is empty or a single line `ℓ` from `ω` downward, and `D` on `ℓ` is
  determined by `ℓ`.
- **Finite cut.** Every vertex's lattice is unbounded in both directions, so its sign changes somewhere. By (Cut) an
  integral vertex would need a `*`, so `I = ∅`.
  - `y` is then the bare cut. Approximate it by translates with cut at `ξ_n -> ξ`, taken from the correct side and
    with denominators finer than every lattice in a given window. Then `L = 0` on the window.
- **Constant sign, `I = ∅`.** Use translates `ξ_n -> ±∞` with fine denominators.
- **Constant sign, `I = ℓ`.** The lattices of `ℓ` are nested cosets whose spacing tends to `∞`. So they meet in at most
  one point `ρ_0 ∈ Z[1/m]`.
  - `E` is determined by `D` except on sites at position `ρ_0`. There the zero chain never ends, and `E ≡ d` is one
    free digit, which is never `*` because there is no `*`.
  - **Approximation.** Use translates whose cut `ξ_n` lies in the lattice of `v_(K_n)`, with `K_n -> ∞` beyond every
    termination level in a given window, and `ξ_n -> ±∞` according to the sign.
  - **If `ρ_0` exists,** take `ξ_n = ρ_0 + s_0 d m^(K_n)` (for `+∞`) or `ρ_0 − s_0 (m − d) m^(K_n)` (for `−∞`). Their
    lowest nonzero digit relative to `ρ_0` is `d` in both cases.
  - The translates then agree with `y` on the window. ∎

## Lesson for general BH

**Layered seeds are rigid by descent.** Three moves make every layer commute:
- **Tree of atoms.** Every deterministic layer that refines along a tree (integrality, digits) is a tree of atoms:
  any two of its events are comparable or orthogonal.
- **Local partitions.** Every event on a vertex is a finite sum of chain atoms plus sign letters at the vertex's own
  sites. This is how the order chain commutes with lines.
- **Descent.** Every recursively defined letter (Toeplitz) is a finite sum of atoms plus a remainder deep in its
  chain. Remainders at equal depth are equal or orthogonal, and a deep enough remainder sits locally next to
  whatever it must commute with.

**For the tower.** No single step needed the derived-subshift reduction, and none needed commutation at distance.
This template should carry the machine layers of the seed tower (T1 and gate 4). Their data are also odometer-like
and recursively defined.
