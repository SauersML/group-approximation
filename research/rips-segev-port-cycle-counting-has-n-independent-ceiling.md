---
rg: 2
id: rips-segev-port-cycle-counting-has-n-independent-ceiling
kind: claim
title: Curvature plus active-coset counting on the port cycle cannot close large N in Steenbock's Rips--Segev core, because the girth-capped window criterion is vacuous for N >= 20 (N >= 14 on all-b^2 faces), so a one-face port cycle labelled by a positive relator survives with an N-independent number L_0 of active cosets, and no active-coset bound A(N) >= L_0 (in particular no bound linear in N) gives a contradiction
distinct_from:
  rips-segev-nine-copy-configurations-carry-no-zero-divisors: that closes N = 9 with windows plus curvature plus the active-coset bound; this shows that the same three ingredients, with any active-coset bound, cannot close any N >= 20, and on the gamma = 42 graph cannot close any N with A(N) >= 42.
  rips-segev-coefficient-free-extremal-copy-lemma-fails: that kills the extremal-copy step on supports alone; this kills the global counting route to every N whatever active-coset bound is supplied, coefficient-aware or not.
  rips-segev-support-method-threshold-is-exactly-q-gamma: that is the exact threshold of the support method for few-line a-supports; this is the ceiling of the port-cycle counting method for covered supports.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this is an obstruction to one route toward it and names the step that remains.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-port-cycle-counting-has-n-independent-ceiling-proof`.
Class-killing obstruction.

**Setting.**  As in `rips-segev-nine-copy-configurations-carry-no-zero-divisors` ([9C]) and its sources.
- (H_N): `alpha (u + w b) = 0` with `alpha, w != 0`, and `supp(alpha u) ∪ supp(alpha w)` lies in `N` copies.
- The *counting method* uses four ingredients:
  - a directed port cycle through `L` distinct active cosets, with label `W` positive in `b`, and a minimal disc
    diagram `D` for its cyclic reduction `W'`;
  - the window criterion [8C] Lemma 3: no window with `E* <= 39` has `n* + max(0, e* - N) >= 2N`;
  - the curvature count of [9C] (at least two faces give `sum over shells (4 - i) >= 6`);
  - an upper bound `L <= A(N)` on active cosets, from any source.
- The method closes (H_N) when every `D` allowed by the window criterion forces `L > A(N)`.

**Theorem (ceiling).**
- (a) For every `N >= 20`, and every `Phi`, no window of any face meets the criterion.  The maximum of
  `n* + max(0, e* - N)` over windows with `E* <= 39` is `39 < 2N`.
- (b) If every `b`-syllable of a face is `b^2`, the maximum is `20 + max(0, 19 - N)`.  So the criterion is vacuous
  on such a face exactly when `N >= 14`.
- (c) Let `c` be a directed cycle of `Phi` of length `m` whose label is a relator `r` of `K`.  The one-face diagram
  with boundary `r` satisfies every constraint the method checks when `N >= 20`, with `L = m`.  In the `gamma = 42`
  graph of item 12, `c = (x_4 x_1)^21` gives `r = (b^2 a^{n})^21` in syllables: `l = 42` and `L = 42`, all
  `b`-syllables `b^2`, and it passes every check when `N >= 14`.
- (d) So for `N >= 20` (resp. `N >= 14` on the `gamma = 42` graph) the method closes (H_N) only with an active-coset
  bound `A(N) < L_0(Phi)`, where `L_0(Phi)` is the least such `m` (resp. `A(N) < 42`).  That bound does not depend
  on `N`.
  - A bound `A(N) = cN + d` closes at most the `N < (L_0 - d)/c`.
  - If `girth(Phi) = g > 42`, windows up to `E* <= g - 3` are allowed.  The thresholds become `2N > g - 3`, but for
    fixed `Phi` they are still constants.
  - The brief step "O(1) dirty cosets per copy, so `A(N) = O(N)`, closes every `N` beyond a small threshold" is
    false as a route, whether or not the per-copy bound holds.  Linear counting can close only a bounded range of
    `N`, never a tail.
- (e) The "`~12N` shell `b`-edges" figure of [9C] §5 uses windows to cap shell lengths.  It holds only while the
  criterion bites (`N <= 19`, and `N <= 13` for `l = 42` shells).  Beyond that the only lower bounds on `L` the
  method yields are constants.

**What it leaves.**  Any proof for large `N` must give a contradiction that is local and does not depend on `N`.
- The target is one shell face `M` whose exterior arc runs through `>= 21` consecutive arc cosets of its copy
  `C_M`, all `b^2` when `l = 42`.
- The rank-one lemma leaves at most one of them pure.  Such an arc is excluded now only by counting how many
  covering copies can meet it (Lemma 2(e) of [8C]), and that count grows with `N`.
- The missing statement is a *coefficient* lemma: the port equations `X(zb) = -Y(z)` cannot hold along `>= 21`
  consecutive impure arc cosets of one copy, whatever the other copies are.  This is the extremal-copy step in
  local form.  `rips-segev-coefficient-free-extremal-copy-lemma-fails` shows it needs coefficients.

Artifact: `experiments/rips-segev-counting-ceiling-2026-09-17/counting_ceiling.py` recomputes (a), (b) and the
closable ranges in (d).
