# bh-verify-master, item 5: the Ã₂ link theorem

`a2-rs-matrices-irreducible-and-primitive-iff-type-transitive` (landed 89194fc49), read on origin/main at
6481dbd30. Adversarial check by lane bh-verify-master, 2026-09-18. Lane check, not an external review.

**Verdict: PASS.** Every step was re-derived.

- **Tiles and successors.**
  - In an apartment, write the base vertex `v` of type τ, then `v+e_1` (τ+1), `v+e_2` (τ+2) and
    `v+e_1+e_2` (τ).
  - The cotypes are then: diagonal τ, the panel shared by `C_1` and `C_2` τ+2, and the panel shared
    by `C_2` and `C_3` τ+1. These match `π_{τ+2}(C_1)` and `π_{τ+1}(C_2)`, and the successor has
    phase τ+1.
  - The cotype word `(τ, τ+2, τ+1)` has three distinct letters, so it is reduced in the affine Weyl
    group of type Ã₂. A non-stammering gallery of reduced type lies in an apartment, giving the
    shape-(2,1) parallelogram.
  - `S(t)` depends only on `(C_1, τ)`, and `P(b)` only on `(C_2, phase)`. Each has `q²` elements.
  - Freeness on vertices makes these `q²` classes distinct: two successors of one tile share their
    base vertex `v+e_1`.
- **Step 1.** A digraph on a finite set with all in- and out-degrees `q²` has no edges between
  strongly connected components (induction from source components). Correct.
- **Step 2.** (m1) holds because the successor sets are equal, and (m2) because the predecessor sets
  are equal. With a third chamber (thickness) they reach every ordered pair on a panel. So one tile of
  𝒯 on a panel puts the whole panel in `𝒫_σ`. Correct.
- **Step 3.**
  - A cotype-τ panel is `(v, x)`, with types τ+1 and τ+2.
  - The successors' diagonals are `(w, y)` with `(v,w,y)` a chamber and `y ≠ x`. This gives (F).
  - Predecessors reverse it, giving (B). Correct.
- **Step 4.**
  - In `lk(v)`, one line `x ∈ L_v` puts every line through each point `w` of `x` into `L_v`, by (F)
    and then (B) with `y ∉ {x, x'}`. Any two lines of a projective plane meet, so `L_v` is empty or
    everything.
  - The dual argument works in `lk(w)`.
  - The graph of edges between types τ and τ+1 is connected: it is a hexagonal lattice in each
    apartment, and any two vertices lie in a common apartment. Correct.
- **Step 5.** A component meets some phase τ, so `𝒫_τ` is everything, and (F) spreads this to every
  phase. So `M_1` is irreducible. `M_2` is symmetric. Correct.
- **Step 6.**
  - The cyclic class `F̃` is constant under (m1) and (m2), so it depends only on the panel, and
    `u(w,y) = u(v,x) + 1`.
  - The pencil argument gives `u(v,·) = U(v)` and `u(w,·) = U'(w)`.
  - One phase later, `u(w,y)` also depends only on `y`. Connectivity of the τ/(τ+2) edge graph then
    makes `u` constant on each cotype.
  - The constants increase by 1 around the three cotypes, so `d | 3`.
  - `d = 3` if and only if `θ = 0`, since the phase is Γ-invariant exactly when `θ = 0`. Correct.

**Minor trust point.** The node takes the combinatorial successor relation (shape-(2,1) continuation) to
be Robertson–Steger's `M_1`, citing arXiv:1302.5593 §7. I did not re-read that source. The theorem is
proved for the successor relation as defined in the node, and the downstream uses in
`rs-two-graph-aperiodicity-from-h3-and-irreducibility` and the BH chain use it in that form. This concerns
the identification only.

## Lesson for general BH

This is a genuinely local-to-global rigidity mechanism. One incidence axiom (any two lines meet) spreads
a closure property from one tile to the whole building, with no ergodic theory. That is the cleanest
positive instance of the synthesis's "cross-depth rule". It is the model to imitate for Conjecture G2-fp:
pencil closure plays the role of "unique local extension".
