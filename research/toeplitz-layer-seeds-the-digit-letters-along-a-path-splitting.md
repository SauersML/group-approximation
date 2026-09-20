---
rg: 2
id: toeplitz-layer-seeds-the-digit-letters-along-a-path-splitting
kind: claim
title: An order seed of (BS(1,m), <a>) enriched by an integrality layer and a Toeplitz lowest-digit layer satisfies (DM) and (EX) along <x>, identical copies satisfy (M), and so edge-pinned gluing along the PATH splitting BS_1 -<x>- BS_2 - ... - BS_k seeds the digit letters F(a) of BS_k(1,m), conditional on rigidity of the enriched vertex seed
distinct_from:
  digit-group-cores-need-m-adic-coherence: that shows the star splitting (a Z centre) and the HNN splitting cannot work, since relative seeds of Z have finite boundary; this uses the path splitting, where the shared line is an edge coset, which needs only an expansive trace, and a Toeplitz layer supplies it.
  ordered-orbits-give-rigid-relative-seeds: that is the plain order seed, which fails (DM) along <x>; this adds three layers that are functions of the forced position and gives (DM) and (EX).
  digit-letters-are-relatively-convex-but-not-positively-connected: that closes the order route for F(a) itself; this uses order seeds only on the vertex groups BS(1,m), where (PC) holds.
---

**Status.**
- §§1–3 are **ESTABLISHED** (lane proof, bh-invent-14, 2026-09-19; elementary; not reviewed): (RS1)
  of the enriched seed, (DM), (EX) and (M).
- §4 (RS2 of the enriched seed) was a lane sketch, and (RS3) was only reduced. **Both are now proved** in
  `toeplitz-enriched-order-seed-is-a-rigid-relative-seed` (bh-invent-03, checked by bh-invent-14).
- So `(Z_J, F(a)) ∈ 𝓡` holds **unconditionally** (lane proofs, not independently refereed).
- Inputs: `ordered-orbits-give-rigid-relative-seeds` (bh-invent-03), with path splitting and (EX)
  concern from the same lane, and `edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy`
  (5c85cfc17f).

**Setting.**
- `V = BS(1,m) = ⟨x, a | a^{-1}xa = x^m⟩` acts on `Z[1/m] ⊂ R` by `x(t) = t+1` and `a(t) = t/m`. So
  `Stab(0) = ⟨a⟩`.
- For a configuration with cut at `ξ`, the *frame position* of `g` is `u(g) = g^{-1}(ξ)`. It
  satisfies `u(gx) = u(g) − 1` and `u(ga) = m·u(g)`.
- `Z_J = BS_k(1,m)` is the path of groups `BS_1 —⟨x⟩— BS_2 —⟨x⟩— ⋯ — BS_k`, with `BS_i = ⟨x, a_i⟩`.
  The presentation is the same as the star or HNN form.

## 1. The enriched seed `Y_E` on `V`

**Letters.** A sign `σ ∈ {+, *, −}`, an integrality bit `L`, a digit `D ∈ Z/m`, and a Toeplitz letter
`E ∈ {1, …, m−1, *}`. `D` and `E` are read only where `L` holds.

**Rules** (all nearest-neighbour).
- **(O)** The order-seed rules of `ordered-orbits-give-rigid-relative-seeds` for `σ`.
- **(L)** `L(gx) = L(g)`. `L(g) ⇒ L(ga)` and `D(ga) = 0`. `L(ga^{-1}) ⟺ L(g) ∧ D(g) = 0`.
- **(D)** `D(gx) = D(g) − 1`.
- **(Tz)** If `D(g) ≠ 0` then `E(g) = D(g)`. If `D(g) = 0` then `E(g) = E(ga^{-1})`. `E(g) = *` iff
  `σ(g) = *`.
- **(Cut)** `σ(g) = *` implies `L(g)`. On an integral coset the sign may change only through `*`: the
  step `(+, −)` on `(g, gx)` is forbidden when `L(g)`.

**The seed** is `σ = *` at `1`. The forced point `y` has cut `ξ = 0` and:
- `L(g) = [u(g) ∈ Z] = [g ∈ ⟨a⟩⟨x⟩]`;
- `D(g) = u(g) mod m`;
- `E(g)` = the lowest nonzero `m`-adic digit of `u(g)`, or `*` when `u(g) = 0`.

**(RS1) and the stabilizer.**
- `σ` is forced by (O).
- `*` sits on `⟨a⟩`, so (Cut) and (L) force `L` on `⟨a⟩⟨x⟩`.
- `L` is false elsewhere. For any `g`, `u(ga^J) ∈ Z` for large `J`, and the biconditional in (L)
  propagates falsity back down the chain.
- `D` is anchored on every integral coset by `D(ga) = 0`. `E` is forced by the well-founded chain
  `u ↦ u/m`, which ends at a nonzero digit or at `*`.
- Every layer is a function of `u(g) = g^{-1}(0)`, which is `⟨a⟩`-invariant. So `Stab(y) = ⟨a⟩`. ∎

## 2. (DM) and (EX) along `⟨x⟩`

- **(DM).** `g ∈ ⟨a⟩⟨x⟩ ⟺ g^{-1}(0) ∈ Z ⟺ L(g)`. So `U = [L(1)]` is a clopen mark for the double coset
  `⟨a⟩⟨x⟩`.
- **(EX).** Put `O = cl(⟨x⟩·y)`, and let the trace `τ(z)(x^r)` be the letter of `z` at `x^r`.
  - `x^s·y` has cut at `s`. Along the line, `E(x^r) = t(s − r)`, where `t(n)` is the lowest nonzero
    digit of `n` and `t(0) = *`. This is the regular `m`-Toeplitz sequence.
  - The limits along `s_n → ±∞` with `s_n → ρ ∈ Z_m` have constant sign `±`. For `ρ ∉ Z` the trace is
    `r ↦ t(ρ − r)`. For `ρ ∈ Z` it has one extra free digit `d` at `r = ρ`, and that same `d` holds on
    the whole zero-chain `a`-ladder, since multiplying by `m^j` shifts digits.
  - The boundary of `O` is therefore a regular Toeplitz subshift over the odometer `Z_m`, times the
    two signs.
  - `τ` is injective on `O`, since Toeplitz sequences determine `ρ` off the orbit `Z` and the `*`
    locates the translates. So `⟨x⟩ ↷ O` is expansive. ∎

## 3. (M), and gluing along the path

- **Vertex pieces.** Every vertex `BS_i` carries the same seed `Y_E` via `x ↦ x`, `a_i ↦ a`.
- **The core.** `F(a) ∩ BS_i = ⟨a_i⟩` (kill `x`), and `F(a) ∩ ⟨x⟩ = 1`. The core of
  `F(a) = ∗⟨a_i⟩` is `F(a)·P`, where `P` is the base path `BS_1, …, BS_k`. Its quotient is the path.
- **Core edges.** At `BS_i` the core edges, in both directions along the path, are the cosets
  `a_i^j⟨x⟩`, i.e. the double coset `⟨a_i⟩⟨x⟩`. This is one datum per direction, marked by `U` (§2).
- **(M).** On the shared edge coset `⟨x⟩ = BS_i ∩ BS_{i+1}`, both endpoint seeds induce the **same**
  `⟨x⟩`-system `O` with the same orbit map `x^s·y_i ↦ x^s·y_{i+1}`. So `Ψ` is the identity.
- **(E).** The pointer seeds `(BS_i, ⟨x⟩) ∈ 𝓡` exist by item 1 of
  `relative-seeds-glue-graphs-of-groups-into-class-c` (`C = V_u`).

**Theorem.** `Y_E` satisfies (RS2) and (RS3) (bh-invent-03's node above), so edge-pinned gluing (5c85cfc17f)
gives a rigid relative seed for `(Z_J, F(a))`.
- **Coherence.** On every core edge coset the trace rule (TR) makes the Toeplitz layers of the two
  endpoints agree letter by letter. So all branches read one `m`-adic position, which is the
  coherence that `digit-group-cores-need-m-adic-coherence` §1 found missing.
- **Consequences.** Through `θ : a_i ↦ a_i x^{-i}` this also gives `(Z_J, Σ)`, and hence the
  `J`-pairs of `kurosh-relative-seeds-and-the-b1-digit-splitting` §4, after one more edge-pinned
  gluing along `t`.

## 4. (RS2) sketch and (RS3) reduction for `Y_E`

**(RS2), sketch.** `L` is up-closed along `a`, and it chooses exactly one integral child along
`a^{-1}`. So the integral set is empty or one line from `ω` to a down-end. The points of `Y_E` are:
- **(i)** the translates;
- **(ii)** cuts at non-orbit points, including one-sided cuts at orbit points, with `L` empty. By
  (Cut), every coset crosses a finite cut, so an integral coset would need a `*`;
- **(iii)** constant signs with `L` empty, or with an integral line `ρ` and its `D`, `E` data, and a
  free `d` on a zero-chain.

Each is a limit of translates: take cuts `ξ_n → ξ` with growing denominators, so the lines escape,
or `ξ_n → ±∞` with `ξ_n → ρ` in `Z_m`.

**(RS3), reduction.**
- `y` is locally forced, so by `quantum-rigidity-is-decided-on-the-derived-subshift` it suffices to
  prove rigidity of `Y_E'`, which is (ii) ∪ (iii).
- Its sign layer is one chain, rigid as in the order seed.
- Its line data (`L`, `D`, and `E` off zero-chains) is a line in the `BS(1,m)` tree plus
  deterministic digits, which is the situation of bh-invent-10's line-sink rigidity.
- The one new item is the free zero-chain digit `d`, a single global parameter propagated by
  `E(g) = E(ga^{-1})`.
- **Not written out:** the commutation of the sign chain with the line atoms.

## Lesson for general BH

**Put the counter on an edge, not a vertex.**
- A relative seed of `Z` has finite boundary, so no cyclic *vertex* can carry an `m`-adic position.
- A cyclic *edge* needs only an expansive trace, and a Toeplitz lowest-digit layer is one: its
  boundary is a Toeplitz subshift over the odometer, which is exactly what an `m`-adic counter
  looks like at scale 1.
- Splitting the digit group as a path of `BS(1,m)` vertices, rather than a star around `⟨x⟩`, moves
  the shared line onto edges. The trace rule then enforces coherence across branches for free.
- **General principle for seed towers:** odometer-type data must travel through edges whose induced
  compactification is Toeplitz, and vertex groups must be rich enough, here `BS(1,m)`, to force the
  Toeplitz layer locally.
