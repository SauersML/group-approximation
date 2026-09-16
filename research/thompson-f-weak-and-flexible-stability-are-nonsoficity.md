---
rg: 2
id: thompson-f-weak-and-flexible-stability-are-nonsoficity
kind: claim
title: Weak, local and flexible permutation stability of Thompson's F each coincide with nonsoficity
distinct_from:
  thompson-f-sofic-iff-relator-system-unstable: that is strict stability of the relators (Arzhantseva--Paunescu Definition 3.2) and its one-commutator form; this adds their weak stability (Definition 7.1), Bradford's four senses and Becker--Lubotzky's flexible senses, all through one commutator transfer inequality.
  thompson-f-relator-system-stable-in-permutations: that is the open strict question; this shows that the "weakly" reading of the same Open problem, and every local or flexible variant, is the same question.
  thompson-v-sofic-iff-not-permutation-stable: that is the dictionary for V, whose finite actions are trivial; F has abelian finite quotients, so its corrections are commuting pairs, and the flexible directions need the transfer inequality.
  sofic-stable-implies-residually-finite: that is the one-directional general principle; this is two-sided for F, with explicit failure constants 1/4 and 1/2.
  infinite-simple-group-permutation-stable-iff-nonsofic: that covers simple groups, corrected to trivial actions; F is not simple.
  character-rigid-fp-simple-groups-stability-dictionary: that is the class of character-rigid simple groups; F is not simple and has the abelian characters of Z^2.
artifacts:
  - research/artifacts/thompson-f-stability-variants-2026-09-16.md
---

Let `F = <a, b | R_1, R_2>` with `R_1 = [ab^-1, a^-1ba]`, `R_2 = [ab^-1, a^-2ba^2]`, `S = {a, b}`,
and let `d` be the normalized Hamming distance. The following are equivalent.
1. `F` is not sofic.
2. `R = {R_1, R_2}` is stable in permutations (Arzhantseva--Păunescu, arXiv:1410.2626v2, Definition 3.2).
3. `R` is weakly stable in permutations (same paper, Definition 7.1). Only `delta`-strong solutions must
   be corrected. These are pairs on which every word `xi` of length `< 1/delta` has
   `d(xi(p), id) < delta` if `xi` lies in `<<R>>`, and `d(xi(p), id) > 1 - delta` otherwise.
4. `F` is stable, weakly stable, locally stable, or weakly locally stable, in Bradford's senses
   (arXiv:2211.15249v2, Definition 1.3 and Remark 1.4). Each one alone suffices.
5. `F` is `P`-stable, `P`-flexibly stable, or `P`-very-flexibly stable (Becker--Lubotzky,
   arXiv:1809.00632, Definition 1.1 and §4.4). Each one alone suffices.
6. Every sofic approximation `f_k : S -> Sym(n_k)` has homomorphisms `g_k : F -> Sym(t_k)`, `t_k >= n_k`,
   with `liminf_k sum_s d^vf(f_k(s), g_k(s)) < 1/2`. Here `d^vf` counts disagreements on `[n_k]` only.

**Transfer inequality.** For `A, B` in `Sym(n)` and `A', B'` in `Sym(t)`, `t >= n`, let `E_A`, `E_B` be
the points of `[n]` where `A, A'` (resp. `B, B'`) disagree. Then `[A,B]` and `[A',B']` disagree on at most
`2(|E_A| + |E_B|)` points of `[n]`, and the constant 2 is sharp. Every homomorphism `F -> Sym(t)` sends
`a, b` to commuting permutations, since finite quotients of `F` are abelian. So a correction of any kind
forces the commutator to be small, while soficity keeps it near fixed-point-free.

## Consequences

- **Both readings of the Open problem.** Arzhantseva--Păunescu ask whether `R` is "(weakly) stable".
  The weak reading is equivalent to the strict one, which is `thompson-f-relator-system-stable-in-permutations`.
- **Explicit failure if `F` is sofic.** Weak stability fails for every `epsilon < 1/4`. Every flexible
  correction of a sofic approximation has `liminf` total error at least `1/2`.
- **Their Conjecture 1.2 holds for `G = F`.** Its hypothesis includes `N = 1`, i.e. item 3, and every other
  quotient of `F` is abelian, hence weakly stable by their Theorem 1.1. Item 3 gives item 2 through
  `3 => 1 => 2`, and the second step is the imported direction.
- **Firewall.** None of items 3--6 is a weaker intermediate target. A proof that `F` is weakly, locally or
  flexibly stable proves that `F` is not sofic unconditionally, and proves the root through direction
  `1 => 2` of `thompson-f-sofic-iff-relator-system-unstable`.

## Scope

- **Unconditional part.** Items 1, 3, 4(weakly stable), 4(weakly locally stable) and 6 are equivalent using
  only the transfer inequality and the classical fact that finite quotients of `F` are abelian
  (Cannon--Floyd--Parry; Fact 1.1 of `research/artifacts/thompson-f-soficity-as-relator-stability-2026-09-12.md`).
  The strict, local and flexible senses need
  direction `1 => 2` of `thompson-f-sofic-iff-relator-system-unstable`.
- **Novelty.** Each implication into item 1 instantiates a known principle for groups that are not
  residually finite: Arzhantseva--Păunescu Theorem 7.2(ii), Bradford Lemma 2.15, and the remark in
  Becker--Lubotzky §4.4. What is new here is one sharp inequality, covering all variants for `F`, and the
  resulting constants. No priority is claimed.

Proof: `thompson-f-weak-and-flexible-stability-are-nonsoficity-proof`.
