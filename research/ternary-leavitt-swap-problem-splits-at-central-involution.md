---
rg: 2
id: ternary-leavitt-swap-problem-splits-at-central-involution
kind: claim
title: The central involution splits the ternary swap corner into a Leavitt-visible Cohn half and a Leavitt-invisible half on the scalar quotient
distinct_from:
  ternary-leavitt-swap-idempotent-is-full: that is the open corner equation c e b = 1 in the group algebra of the ternary unit group; this is the established splitting of that equation along the central involution into two halves, each of which alone refutes Gottschalk, with the Leavitt evaluation seeing only the anti-central one.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Let `R = L_(F_3)(1,2)`, `G = R^x`, `S = F_3[G]`, `z = -1` (central, order two),
`PG = G/<z>`, `w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1` and `e = 2(1 + [w])`.

1. `eps_(+-) = 2(1 +- [z])` are central orthogonal idempotents with sum `1`, so
   `S = S_+ x S_-`. Here `S_+ ~= F_3[PG]`, and `[z]` acts as `-1` on `S_-`.
2. `d^2 = 1` and `d w d = z w`, so `[d]` conjugates `e_- = eps_- e` to
   `eps_- - e_-`. Hence `S_- ~= M_2(T)` with `T = e_- S_- e_-`, and `S_-` has no
   unital homomorphism to a nonzero commutative ring.
3. `c e_- b = eps_-` is solvable in `S_-` iff `T` contains a unital two-pair Cohn
   family `gamma_i beta_j = delta_ij`.
4. The Leavitt evaluation `F_3[G] -> R` sends `[z]` to `-1`, so it factors through
   `S_-` and kills `S_+`.
5. `c e b = 1` in `S` implies `cbar ebar bbar = 1` in `F_3[PG]`, with
   `ebar = 2(1 + [wbar])`. That equation alone makes `PG` nonsurjunctive, through
   an injective linear automaton with `<wbar>`-invariant output.
6. *(Corrected 2026-09-12 by gk-verify-pos.)* A solution of `c e_- b = eps_-` in
   `S_-` alone also suffices.
   * With `A = e_- b + eps_+` and `C = c + eps_+`, `CA = 1` and `AC != 1`, because
     `e_- != eps_-`.
   * So `F_3[G]` is not directly finite, and `G` is not surjunctive, hence neither is
     `PG`, which contains a copy of `G` (Corollary 8.2 of the artifact).
   * The automaton is the identity on the summand `x(gz) = x(g)` and strict on the
     complementary summand `x(gz) = -x(g)`.

So lifting the Leavitt solution `b = s0 + s1`, `c = 2(t0 + t1)` addresses `S_-`, and
that half is sufficient (`ternary-anti-invariant-swap-corner-is-full`). The other
sufficient half is `projective-ternary-swap-idempotent-is-full`, on which the Leavitt
evaluation vanishes. Proof: Section 7 of the artifact, with correction 7.4(e).
