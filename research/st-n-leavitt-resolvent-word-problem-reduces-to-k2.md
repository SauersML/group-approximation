---
rg: 2
id: st-n-leavitt-resolvent-word-problem-reduces-to-k2
kind: claim
title: For every N >= 4 the word problem of St_N(R_L) is decidable exactly when nontriviality in K_2(N,R_L) is recursively enumerable, and it is decidable if K_2(N,R_L) injects into stable K_2(R_L) with a computable complete invariant
distinct_from:
  steinberg-resolvent-shell-envelope-is-finitely-presented: that route needs St_N(R_L) (N = 4, or N >= 5 such as N = 10) to have solvable word problem as its gate 1; this checks the lane remark on E_N(R_L) and reduces the gate to a statement about K_2(N,R_L).
  k2-central-in-steinberg-groups-of-leavitt-resolvent-ring: that asks for centrality of K_2(N,R_L), N >= 5; this needs injective stability at N, which implies centrality there.
artifacts:
  - research/artifacts/gq-gq-typea-design-u2-germ-implant.md
---

**ESTABLISHED (2026-09-18)** for items 1–3 through `st-n-leavitt-resolvent-word-problem-reduces-to-k2-proof`.
Lane proof (gq-k2-q), elementary, not independently reviewed. Item 4 is OPEN.

## Statement

Let `R_L` be the ring of `leavitt-resolvent-ring-is-fp-simple-of-char-zero`, let `N >= 4`, and let `K_2(N,R_L)` be
the kernel of `St_N(R_L) -> E_N(R_L)`. Items 1–3 hold for every such `N`. They are used for `N >= 5` (for example
`N = 10`) by the shell route, and hold for `N = 4` as well.

1. **The lane remark holds.** `R_L` has solvable word problem, and so does `E_N(R_L) ≤ GL_N(R_L)`, with respect to
   the generators `e_ij(g)` for `g` among the six ring generators and `1`. This part needs only `N >= 3`.
2. **Reduction.** `St_N(R_L)` is finitely presented for `N >= 4`
   (`steinberg-finite-presentation-and-kazhdan-theorem`), so its trivial words are recursively enumerable.
   - Its word problem is solvable if and only if the set of nontrivial words whose image in `E_N(R_L)` is `1` is
     recursively enumerable.
   - In other words: if and only if nontriviality in `K_2(N,R_L)` can be certified.
3. **A sufficient condition.** Suppose:
   - (i) injective stability at `N`: `K_2(N,R_L) -> K_2(R_L)` is injective;
   - (ii) there is a computable homomorphism `ι : K_2(R_L) -> H` into a group with solvable word problem, injective
     on the image of `K_2(N,R_L)`. Computable means: from a word of `St_N(R_L)` in `K_2(N,R_L)`, compute a word for
     its image in `H`.

   Then `St_N(R_L)` has solvable word problem. In particular this holds if (i) holds and stable `K_2(R_L) = 0`,
   since then `St_N(R_L) ≅ E_N(R_L)`.
4. **Open.** Neither (i) nor (ii) is known, for any `N`.
   - `R_L` has infinite stable range, so no stability theorem gives (i). A replacement would be a Morita-type
     comparison: `R_L ≅ M_2(R_L)` gives `St_N(R_L) ≅ St_N(M_2(R_L))`, to be compared with the block map to
     `St_(2N)(R_L)` (`k2-central-in-steinberg-groups-of-leavitt-resolvent-ring`).
   - Stable `K_2(R_L)` is not computed here. The following is heuristic, and conditional on the Pimsner sequence
     `(P)` for `R_L` over its diagonal base `B`, the functions of the number operator. Here the ring generator `N` of `R_L` is
     meant, not the rank.
     - `[X] = σ_* + ev_(0,*)`, from `t_1 N s_1 = N + 1` and `t_2 N s_2 = 0`.
     - `1 − [X]` is then `−1` on `K_0(B)`, but it is not invertible on `K_1(B)` or `K_2(B)`, because the resolvents
       `N + k` carry tame symbols.
     - So stable `K_2(R_L)` need not vanish.

## Reading

- The central lifts of `Q^x·I_N` (05eb02b9f) are elements of `St_N(R_L)` over central scalar matrices, not
  elements of `K_2(N,R_L)`. They bear on centrality, not on this membership question.
- Nothing here gives undecidability. An obstruction (b) would need a non-recursive `K_2(N,R_L)`-membership built
  from the ring's finitely many relations. No mechanism for that is known.
## Attempts
1. **Stable `K_2(R_L)` computed, 2026-09-18 (lane gq-infinite-primes).**
   `leavitt-resolvent-k-theory-is-shifted-rational-k-theory`. With the vacuum projections `q_k` in the base, `R_L`
   satisfies the hypotheses of `register-completion-pimsner-from-supercoherence`. So the heuristic of item 4 is a
   theorem: `K_n(R_L) ≅ K_(n-1)(Q)` for every `n`, and `K_2(R_L) ≅ Q^x` through `{λ, N+1} -> λ`.
   - `K_2(N, R_L) -> K_2(R_L)` is onto for every `N >= 3`, and `E_N(R_L)` is not finitely presented.
   - The shortcut "(i) and `K_2 = 0`" is closed.
   - Under (i), (ii) asks for a computable form of `K_2(N, R_L) -> Q^x`. That is open.
