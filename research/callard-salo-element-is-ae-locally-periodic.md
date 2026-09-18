---
rg: 2
id: callard-salo-element-is-ae-locally-periodic
kind: claim
title: "The Callard--Salo distortion element of mV is Lebesgue-a.e. locally periodic, with germ size bounded by its conveyor-belt length uniformly in the power"
distinct_from:
  brin-thompson-mv-contains-a-distortion-element: that imports the word-norm bound |f^N| = O(log^4 N); this records the measurable dynamics of the same element (a.e. finite orbits, uniformly bounded germs), which the distortion statement does not mention
  heisenberg-in-nv-forces-drift-free-central-element: that is about drift of central elements of embedded Heisenberg groups; this is about the specific element produced by Callard--Salo's proof
---

**Statement.** Let `m ≥ 2` and let `f ∈ mV` be the distortion element produced by the proof of
Theorem E of Callard–Salo (arXiv:2208.00685). That element is the image of `f_SMART` (their
Lemma `lem:better-bounds-for-smart`), restricted to one-head configurations, under their embedding
chain `RTM(18,96) ≤ RTM(18+t, 96+ℓ) → RTM(n,k) → RTM(n,1) → 2V → mV` (Lemma `lem:TMin2V`). Let
`λ` be the Haar (Lebesgue) measure on `C^m`. There are a measurable function `L : C^m → N ∪ {∞}`
and constants `C, q < 1` such that:

1. `λ(L ≥ ℓ) ≤ C (ℓ+1) q^ℓ`. In particular `L < ∞` a.e., and `∫ L^d dλ < ∞` for every `d`.
2. Every `x` with `L(x) < ∞` has a clopen brick neighbourhood `U_x` and an integer
   `P(x) ≤ exp(C (L(x)+1))` with `f^{P(x)} = id` on `U_x`.
3. For every `N ∈ Z` and every such `x`, `f^N` is canonical on a brick containing `x` whose
   address, together with the address of its image, has total length at most `C (L(x)+1)`. So
   the per-coordinate exponent cocycle obeys `|c(f^N, x)| ≤ C (L(x)+1)` uniformly in `N`.

**Why it matters.** Distortion forces every proper cnd function to grow along `⟨f⟩`. But `f` is
measurably a "locally finite" element: a.e. it acts through finite permutations of cylinders whose
periods are exponential in a geometrically distributed size. So any growth of a cnd function
along `f` must come from exponentially rare regions carrying exponentially large weight. This is
the odometer-type behaviour that the Lévy–Khintchine analysis of `ψ|⟨f⟩` predicts.
`nv-local-density-walls-bounded-on-callard-salo-element` is the consequence for integrated walls.

## Attempts

- 2026-09-17 (e-nv-walls, swarm-0917). *Argument; OPEN only because the embedding chain is
  outlined, not written out, in the source.* The source was read from the arXiv e-print
  2208.00685v3 (tex source, files `distortion-0-main.tex` and `distortion-3-automorphism.tex`).
  - **Conveyor belts (verbatim, Sec. "Conveyor belts").** Any configuration splits into belts
    `w_i ∈ (Γ²×{+1})^* (head cell) (Γ²×{−1})^*` or `(Γ²×{+1})^+ (Γ²×{−1})^+`. Verbatim: "This can be
    summarized as: $f_\mathcal{M}$ considers such words as a cyclic tape folded in the shape of a
    conveyor belt, and acts on the cyclic tape." Also verbatim: "Note that $x$ and
    $f_\mathcal{M}(x)$ have the same decomposition into a product of conveyor belts".
  - **Restriction to one head (verbatim, proof of the Turing-machine theorem).** "Consider the
    sofic subshift $Z$ where a symbol of $(Q' \times \{+1, -1\} \times \Gamma^2)$ can appear at
    most once. We clearly have a conjugacy $Z \cong X_{96} \times Y_{18}$". Also: "our generators
    only act near the head, so by definition this restricted action makes them elements of
    $\RTM(18, 96)$."
  - **Step A (belt invariance).** In the one-head model the head's belt `B(x)` is the maximal run of
    `+1` cells to its left, together with the maximal run of `−1` cells to its right. Let `L(x)` be
    its length. `f` preserves the belt decomposition and acts on `B(x)` as a reversible machine on a
    cyclic tape of length `2L(x)`. Every other cell is untouched, and the head never leaves `B(x)`.
    The later steps of the chain preserve this:
    - Adding the symbols `S` and the `ℓ` extra states: new symbols are "new empty conveyor belts of
      size 1", and the new states act as the identity.
    - Blocking: `m`-blocks become cells and the word at the origin becomes part of the state.
    - Binary codes: a complete suffix code `C` and a complete prefix code `D`.
    Each step is a conjugacy onto an invariant set, or an extension by the identity. Each changes
    lengths by at most a constant factor.
  - **Step B (item 2).** Let `U_x` be the cylinder fixing the state, the contents of `B(x)` and the
    two border cells. `f` permutes the finitely many cylinders with the same belt shape; there are
    at most `|Q|·(2L)·|Σ|^{2L}` of them. So some `P ≤ exp(C(L+1))` fixes `U_x` setwise. Then `f^P`
    is a canonical map `U_x → U_x` between equal addresses, so it is the identity.
  - **Step C (item 3).** Each `f^N` maps `U_x` canonically onto `U_{f^N x}`. That is a cylinder of
    the same shape, with address length `O(L+1)` in each binary coordinate, because code words
    have bounded length. This gives the germ bound and `|c(f^N,x)| ≤ C(L+1)`.
  - **Step D (item 1).** Under the parsing homeomorphism of Lemma `lem:TMin2V`, `λ` pushes forward
    to a product measure on cells in which each symbol `a` has probability `2^{−|D(a)|}` (or
    `2^{−|C(a)|}` on the left), so every symbol has positive probability. Blocks are i.i.d. with
    full support. So each left `+1` run and each right `−1` run has a geometric tail with ratio
    `q < 1`.
  - **Gap to close for ESTABLISHED.** Write out the transport of Steps A–C through the block
    embedding `RTM(n^m, k n^m) → RTM(n,k)` and the state encoding `RTM(n, n^j) ≅ RTM(n,1)`. Both
    are only sketched in the source ("by considering $m$-blocks of cells as individual cells", "by
    moving by $m$ steps at once"). Nothing there can move the head outside the image of its belt,
    but it has not been written cell by cell.
  - **Computation.** `experiments/nv-measured-walls-2026-09-17/smart_belt_periods.py` checks that
    the SMART table transcribed from the tikz diagram is reversible. On cyclic tapes of length
    `c = 2, 4, 6, 8, 10`, `T_SMART` has exactly 4 cycles, each of length `2c·3^c`: 36, 648, 8748,
    104976, 1180980 (output in `smart_belt_periods.out`). So belt periods really are exponential in
    the belt length (for undecorated SMART), and item 2's bound is sharp up to constants. The
    decorated `f_SMART` has 96 states instead of 8, which changes only the constants.
