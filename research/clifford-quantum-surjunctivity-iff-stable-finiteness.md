---
rg: 2
id: clifford-quantum-surjunctivity-iff-stable-finiteness
kind: claim
title: Every Clifford quantum automaton over G on qudits of prime dimension p is onto exactly when F_p[G] is stably finite
distinct_from:
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided inverse into a strict classical linear automaton; this turns it into a strict quantum Clifford automaton through the symplectic doubling diag(A, B^*), and proves the converse for Clifford automata unconditionally.
  stable-finiteness-forces-prime-power-surjunctivity: that is the open classical direction for nonlinear automata on p-power alphabets; this is the quantum Clifford sector, where the converse is a two-line computation because the *-homomorphism condition hands over a right inverse.
  quantum-surjunctivity-conjecture: that asks for all quantum automata; this settles the Clifford sector of it and shows that the conjecture contains Kaplansky stable finiteness over every prime field.
  self-similar-clifford-quantum-expander-tape: that builds a Clifford expander tape for complexity purposes; this classifies non-surjective Clifford automata on group lattices.
---

**ESTABLISHED** (route `clifford-quantum-surjunctivity-iff-stable-finiteness-proof`).

**Setting.** Let `p` be prime, `G` a group and `n >= 1`. Let `A = (x)_(G x [n]) M_p`.
- For `u = (a, b)` in `F_p[G]^n (+) F_p[G]^n`, viewed as row vectors of finitely supported functions, `W(u)` is the
  Weyl operator `(x)_(g,i) lambda X^(a_i(g)) Z^(b_i(g))`.
- `lambda = 1` for odd `p` and `lambda = i^(ab)` sitewise for `p = 2`, so that `W(u)^p = 1`.
- A *Clifford automaton* is a shift-equivariant, finite-propagation, unital *-endomorphism `Phi` of `A` that sends
  each `X` and `Z` at the sites `(e, i)` to a scalar multiple of a Weyl operator.

**Statement.**
1. **Clifford automata are symplectic matrices.** There is a unique `M` in `M_(2n)(F_p[G])` with
   `Phi(W(u)) = (phase) W(uM)` for all `u`, and `M J M^* = J` with `J = [[0, -I], [I, 0]]`. Here `*` is conjugate
   transpose under `g -> g^-1`. Conversely, every `M` with `M J M^* = J` is realized by a Clifford automaton.
2. **Onto iff unit.** `Phi` is onto if and only if `M` is left invertible, and then `M^-1 = J M^* J^-1`.
3. **Equivalence.** Every Clifford automaton over `G` with prime dimension `p`, for every `n`, is onto if and only
   if `F_p[G]` is stably finite.

**Consequences.**
- The quantum surjunctivity conjecture implies Kaplansky stable finiteness over every `F_p`. So it is at least as
  hard as the positive-characteristic Kaplansky problem, exactly like the classical conjecture through
  `stable-finiteness-failure-refutes-surjunctivity`.
- Every one-sided inverse `AB = I != BA` over `F_p[G]` gives a strict classical automaton and a strict quantum
  automaton on the same group. This is the linear sector of the transfer premise
  `strict-automata-yield-strict-quantum-endomorphisms`.
- For `G = F_2` and propagation `{1, a, b}`, the artifact enumerates all Clifford automata for `p = 2, 3, 5`. Each
  one is a shift composed with an on-site Clifford gate: 18, 72 and 360 solutions, equal to `3 |Sp_2(F_p)|`.

**Artifacts.** Script `experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2.py`, with output
`experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2-output.txt`.

**Referee (2026-09-17, ref-04): sound.**
- Checked the route line by line: `W(u)^p = 1` for both parities of `p` (the `i^(ab)` phase for `p = 2`), the
  commutation form `beta(u, v) = eps(u J v^*)`, vanishing of every coefficient of `M J M^* - J` from `u = g e_k`,
  `v = e_l`, the realization of `M` through the universal presentation of `M_p`, the right inverse
  `J M^* J^-1`, the trace-orthogonality argument for "not left invertible implies not onto", and the block
  computation for `diag(A, B^*)`.
- Literature: for `G = Z^s` the correspondence between Clifford QCA and symplectic matrices over Laurent polynomials
  is due to Schlingemann, Vogts and Werner, "On the structure of Clifford quantum cellular automata",
  arXiv:0804.4447. The classical linear analogue, "`G` is L-surjunctive iff `K[G]` is stably finite", is in
  Ceccherini-Silberstein and Coornaert, "Cellular Automata and Groups" (Springer, 2010), Chapter 8 on linear
  cellular automata. The route is a direct transfer of these ideas to
  arbitrary `G`, and its framing does not claim otherwise.
