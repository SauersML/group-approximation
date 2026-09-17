---
rg: 2
id: positive-f-folded-fatgraphs-have-only-even-valence
kind: claim
title: For a positive automorphism, every vertex of an f-folded fatgraph off the special bivalent vertices has even valence with alternating signs, which kills legal certificates when a sign has one gate
distinct_from:
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the injectivity criterion; this is an obstruction to its certificates, plus an exact per-word LP that decides them.
  automorphism-immersion-representatives-have-finite-order: that kills the immersion hypothesis on f; this constrains the fatgraphs of the legal criterion that replaces it.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/ffold.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/search2.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/search3.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp5.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/exact_farkas.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/turn_graph_obstruction.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/census_turn_graph.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/scan4.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/phi_scan4.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_t4_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_t4_m2.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_t4_m2_rerun14.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_plastic_m1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_plastic_m4.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_census.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/probe_auts.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/probe_auts.log
---

**ESTABLISHED** (theorem parts 1--4). Proof in `positive-f-folded-fatgraphs-have-only-even-valence-proof`.
Part 5 is a computation with a runnable script and a precise scope.

Let `phi` be a positive automorphism of `F_n` (every `phi(x_i)` is a positive word),
realised on the rose by `f`. Let `X` be an `f`-fatgraph satisfying conditions
(2), (3), (4) of Calegari--Walker's `definition:f_folded` (arXiv:1212.2618, l.972--985).
Call a vertex *special* if it is 2-valent and carries one `f`-corner and one `partial^-`
corner.

1. **Sign parity.** Every corner of `partial S(X)` at which the boundary word changes sign
   sits at a special vertex. Every non-special vertex has even valence, and its outgoing
   directions alternate in sign.
2. **Gate bound.** If moreover `X` is legal (condition (L) of
   `legal-f-folded-fatgraphs-give-surface-subgroups`), every vertex has valence
   `<= 2 min(g_+, g_-)`, where `g_+` and `g_-` count the gates of positive and of negative
   directions. So **if `min(g_+, g_-) <= 1`, every legal `f^m`-folded fatgraph, for every power
   `m`, has `chi = 0`**, and the criterion produces no surface for that `phi`.
3. **Turn-graph bound.** A legal vertex of valence `>= 4` needs a path
   `p_1 - N_1 - p_2 - N_2` in the graph of turns taken inside the words `f(x_i)`, with
   `p_1, p_2` positive directions in distinct gates and `N_1, N_2` negative directions in
   distinct gates.
4. **Periodic sign-change turns.** The sign-change turns of the `partial^-` words form a
   multiset that `Df` permutes. So they are all `Df`-periodic turns.
5. **Exact per-word LP.** For boundaries made of `N` copies of one legal cyclic word `w`
   (with `partial^+ = N` copies of `f(w)^{-1}`), the LP in `lp5.py` is a necessary condition
   for a legal certificate with `chi < 0`, for every `N`. `exact_farkas.py` proves infeasibility
   in exact integer arithmetic. Results:
   - `phi_4 = (a -> bbc, b -> bbcb, c -> cbba)`, charpoly `t^3 - 4t^2 + 1`, which is fully
     irreducible and atoroidal by the matrix test in the proof. At `m = 1`, all 4240 legal
     primitive zero-homology cyclic words of length `<= 10` are certified infeasible. At `m = 2`,
     all 324 words of length `<= 8` are certified: 310 in `farkas_t4_m2.log`, and the 14 on
     which plain rounding failed by exact active-set snapping in `farkas_t4_m2_rerun14.log`.
   - `phi_P = (a -> b, b -> c, c -> ab)`, charpoly `t^3 - t - 1`. At `m = 1`, all 4240 words
     of length `<= 10` are certified. At `m = 4`, all 324 words of length `<= 8` are certified.
   - Census (`scan4.py`, `turn_graph_obstruction.py`): 6420 positive automorphisms of `F_3` with
     images of length 2--4, primitive, with irreducible characteristic polynomial and at least 4
     gates. Part 2 kills 1044 of them for every power. All 5376 others have the turn-graph path
     of part 3, so part 3 kills none of them.
   - Controls: the endomorphisms `a -> ab, b -> ba` (Sapir's group) and `a -> abb, b -> ba` give
     LP optimum `chi = -4` at `m = 2`, and `exact_farkas.py` finds no certificate there, as it must.

**What it rules out.** Legal `f^m`-folded surfaces for positive automorphisms with a
single-gate sign, for every power. For the two named automorphisms, it rules out single-word
certificates in the listed ranges. It does not rule out boundaries made of several different
words, longer words, or larger powers.
