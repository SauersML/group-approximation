---
rg: 2
id: rokhlin-window-transport-is-dominated
kind: claim
title: The random-order transport of every Bernoulli window configuration into one output is at most that output's entropy
distinct_from:
  injective-ca-random-order-transport-is-dominated: that is the automaton-level normal form of full site entropy for injective automata; this is the window-level normal form of Bernoulli Rokhlin maximality, for arbitrary configurations.
  bernoulli-witness-information-is-bounded-by-code-reads: that proves the transport sum is at most m H(psi); this asks for the constant 1.
artifacts:
  - research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md
---
**OPEN.** For every countable group `G`, every configuration `(k, E, F, psi)`, `x` iid uniform on `(A^k)^G`, and i.i.d. order labels `U`:

    sum_(f in F) I( x(f^-1) ; y_1 | y_(f^-1 F ∩ past(1)), U ) <= H(y_1) .

By `rokhlin-window-random-order-transport-identity` the left side is `I(x(1); y_F)`. So this claim is equivalent to `bernoulli-rokhlin-entropy-maximal-for-every-group`, through `bernoulli-rokhlin-deficit-has-a-finitary-witness`. The two routes form an intended cycle, and this claim is a normal form.

A bound `<= C H(y_1)` for one constant `C` gives `rho_q(G) >= log q / C`. On a host with `h_sup in {0, infinity}`, that is INF (artifact Corollary 2).

## Attempts
- **Reading sunflowers.** Suppose every codeword reads site `1` and the windows meet only at `1`. Then the sum is at most `H(y_1)`, by conditional independence and superadditivity (artifact Proposition 3). So a witness needs non-readers or overlapping windows.
- **Linear codes.** Affine `psi` over a field satisfies the bound on every incidence pattern. The proof evaluates the decoding functionals on constant inputs (artifact Proposition 4).
- **Cancellation is used.** A star whose petals read the center at one position has `Phi -> 0` with a pointer code (artifact Example 5). It occurs in no group, so a proof must use right cancellation.
- **Codeword Følner count.** `Phi >= log q / lambda(F)`, where `lambda(F) = inf_S |SF|/|S|`. So the bound holds whenever `<F F^-1>` is amenable (`bernoulli-window-codeword-folner-ratio-bound`). This is the finite-count step. For a nonamenable `<F F^-1>` it loses a constant factor.
- **Per-term bounds.** Each term is at most `H(y_1)`, which gives the bound `|F| H(y_1)`. The read-degree bound `m H(psi)` comes from an order that is not translation-invariant (artifact Section 3).
- **Random past.** Seward's upper bound, as quoted by Alpeev (arXiv:1705.08559, Theorem 1.1), makes the goal equivalent to random-past entropy `>= k log q` for every generating partition. Finite truncations of the chain rule pay a boundary term that vanishes only along Følner sets, and the order has no infinite form (artifact Section 6).
- **Associativity is used (w7-inf-cancellative, 2026-09-12).** This is `cancellative-incidence-patterns-do-not-force-domination`, held OPEN pending verification.
  - A shared-pointer parity gadget satisfies (L) and (R), is realized in a finite loop, and has `Phi <= (log2 k + 1 + 1/k)/k`.
  - No group realizes it. Pointer sharing makes the codewords `c_1, c_1 delta, c_1 delta^2`, and `(1 + delta)(1 + delta + delta^2) = 0` in `F_2[G]` contradicts the value XOR.
  - So a proof must use associativity through translation invariance, not only cancellation, division or a closed finite index set.
  - Counting on the loop gives domination on average over sites but not at `o`.
  - On `T_3` fixing an end, a homogeneous pointer code has `Phi -> 0` but violates (R). Right-cancellative downward windows embed in the free monoid and are dominated.

  Artifact `research/artifacts/right-cancellative-pattern-firewall-2026-09-12.md`.
- **Pointer-gated linear codes: the linear part dies on directly finite group rings
  (a-gs-window-transport, 2026-09-17).** This is `gated-diagonal-linear-deficits-force-kaplansky-failure`.
  - **Exact split.** For `psi = (J(p), L_J(v))`, with pointer bits split from value bits,
    `I(x(1); y_F) - H(y_1) = [I(p(1); J_F) - H(J_1)] + log q (E d - E r)` on every pattern.
  - **The bound.** For monomial-diagonal gating (fixed `T_i ∈ F_q[G]` per coordinate), a recovering
    combination is a left inverse of `T_i`. If `F_q[<E ∪ F>]` is directly finite it is the unique
    `T_i^{-1}`, and stationarity gives `E d <= E r`.
  - **What dies.** An abelian homomorphic pointer has `I(p(1); J_F) <= H(J_1)` by characters on
    constants. So the star and parity-gadget recipes satisfy (D) on every pattern of every such host,
    including linear sofic groups and Higman's group.
  - **What survives.** A deficit in the class exhibits a one-sided unit in `F_q[G]`. By Seward
    Corollary 4.1 that already gives `rho_{q'}(G) = 0`, so the class cannot give first evidence.
  - **Calibration.** In the firewall loop the split gadget has `E d ≈ 3.87` against `E r = 1`, so
    associativity enters exactly through uniqueness of inverses.
  - **Where it stops.** Gating that mixes coordinates, several functionals per coordinate, or
    non-monomial routing. There left inverses of columns are not unique and traces only give `dim` mod
    `p`. This is the OPEN `pointer-gated-linear-codes-are-rank-dominated`, which holds over finite
    groups by counting.

  Artifact `research/artifacts/pointer-gated-linear-witness-direct-finiteness-2026-09-17.md`.
- **Quadrangle closure is not enough (swarm-0917-w5-pull2-gottschalk-1, 2026-09-17).** This is
  `quadrangle-closed-patterns-do-not-force-domination`. It answers the open question of
  `quadrangle-closure-kills-shared-pointer-parity-gadgets` negatively.
  - **The gadget.** An abstract pattern with (L), (R) and (Q) has `Phi = (t + 1 + k(1-1/k)^R)/k -> 0`
    (`0.7817` at `k = 4`).
    - Each gadget has three codewords that rotate one pointer cycle `Z/L` by `a, a, -2a`. The rotation is
      open, so there is no coherent 3-shift and the mod-3 invariant does not apply.
    - The value table follows a Hamiltonian cycle `x -> x + c_rho` of `Z/n`, and `o` is the only site read
      once.
    - All translation types `±a_rho, ±2a_rho` and value differences `±c_rho` are distinct, which makes the
      classes disjoint or equal.
  - **What fails.** Only holonomy. The class word `(tau sigma)^m sigma` fixes a value position and
    translates every pointer by `-(3m+2)a`. In a group, `g^L = g^(3m+2) = 1` forces `g = 1`.
  - **Where it dies.** Any proof of this claim through finite incidence axioms of the pattern alone ((L),
    (R), (Q), counting over the pattern) is killed. A proof must use class words of unbounded length, such as
    (H): a class word with a fixed point is the identity on its domain.
  - **Still open.** Do (L)+(R)+(Q)+(H) force domination?
  - Artifact `research/artifacts/quadrangle-closed-pattern-firewall-2026-09-17.md`. Check
    `experiments/quadrangle-firewall-2026-09-17/verify_rotation_gadget.py`: brute-force (Q), 0 violations;
    decoding, 0 errors.
- **Holonomy kills gadget-local decoders (swarm-0917-w6b-w6b-re-pull2-gottschalk-2, 2026-09-17).**
  This is `holonomy-quadrangle-patterns-have-unique-local-decoders`, ESTABLISHED. It partly answers the
  "still open" question above.
  - **Theorem A.** On every (L)(R)(Q)(H) pattern with a split `E = U ⊔ V`, every site has a linear local
    decoder in at most one gadget, and that decoder is unique.
    - (H) gives a global potential `φ: C -> Π ≤ Sym(U)` on each value component.
    - (Q) makes the value relations `D_g` global.
    - The decoder pushes forward to a unit of `F_q[Π]`.
    - Two gadgets must then read `o` in the same intrinsic columns with different rows, which violates (R).
  - **Consequence.** Every gadget-local amplification firewall, including every (H)-respecting repair of
    the rotation gadget, has `Phi >= log q`.
  - **Where it dies.**
    - **Invariant:** unit-ness of `s_ρ ∈ F_q[Π]`.
    - **Step:** the reader-column collision against (R).
  - **Still open, narrowed.** Do (L)(R)(Q)(H) force domination? A split gated linear witness must now use
    **mixed-pointer decoders**, meaning rows with different pointer sets that cancel across gadgets. This is
    the same survivor as the group-level `coset-local-decoders-force-gated-domination`.
  - Artifact `research/artifacts/holonomy-quadrangle-local-decoder-uniqueness-2026-09-17.md`. Check
    `experiments/holonomy-local-decoders-2026-09-17/check_local_decoders.py`:
    - all 62 (L)(R)(Q) rotation-family members with multi-gadget decoders fail (H);
    - 0 violations on 600 random patterns.
