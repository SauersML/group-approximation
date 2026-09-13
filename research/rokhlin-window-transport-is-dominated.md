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
