---
rg: 2
id: coboundary-expanding-hosts-cannot-carry-shift-ugc
kind: claim
title: Counting non-flat short cycles decides Gap-Shift[1 - eps, delta] over every finite group in polynomial time on any host whose cycle system has congestion M and coboundary expansion beta with M eps < beta (1 - delta), so every UGC route through shift games must output hosts with cycle-test cost M/beta >= (1 - delta)/eps, an H^1 invariant independent of lambda_2 and of threshold rank
distinct_from:
  spectral-gap-ratio-reductions-cannot-prove-ugc: that gates lambda_2, an h^0 (Cheeger) invariant of the constraint graph, by the AKKSTV rounding; this gates the 1-coboundary expansion of the graph plus short cycles, an h^1 invariant, by a cycle-holonomy count. The windmill in item T3 has lambda_2 -> 0 at bounded cycle-test cost, and high-girth expanders have lambda_2 bounded below at infinite cycle-test cost.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that gates the number of large label-extended eigenvalues; the windmill of T3 has threshold rank s -> infinity and cycle-test cost exactly 1.
  unique-games-reduce-to-shifts-over-their-holonomy-group: that uses the holonomy group of all cycles to identify shift games; this uses holonomy of short cycles only, as a local test, and its conclusion is an algorithm and a reduction gate.
  unique-games-lift-to-group-shift-games-on-the-same-host: that transfers general UG to group-shift games at a loss k! in completeness; this kill lives at completeness 1 - eps, where that loss is fatal, so it covers shift games only (T4).
  entanglement-sound-soundness-cannot-prove-ugc: that kills soundness analyses; this kills output host shapes at the YES case.
  group-shift-games-easy-on-globally-hypercontractive-graphs: that is the Bafna--Minzer algorithm transferred to group shifts on hypercontractive hosts; this is an elementary test that needs no hypercontractivity, and it works for every group uniformly.
artifacts:
  - experiments/ugc-coboundary-kill-2026-09-17/check_coboundary_test.py
  - experiments/ugc-coboundary-kill-2026-09-17/output.txt
---

**ESTABLISHED.** Proof: `coboundary-flatness-test-proof`. It is self-contained
and elementary; it imports nothing. `ugc-is-equivalent-to-affine-ugc` (KKMO) is
used only in the *Bearing* paragraph.

**Setting.** `A` is a finite group whose elements have unique encodings with
multiplication and inversion computable in polynomial time (for example `Z_q`,
`F_2^N`, or a permutation group). A **shift game** `(G, b)` over `A` is a
connected multigraph `G = (V, E)` with a probability distribution `mu_E` on
`E`, each edge oriented as `e = (u, v)` and carrying `b_e in A`; the constraint
reads `x_v = b_e x_u`, and traversing `e` backwards uses `b_e^(-1)`.
`val(b) = max_x mu_E{e : x_v = b_e x_u}`.

* `B^1(G; A)` is the set of coboundaries `(dx)_e = x_v x_u^(-1)`, and
  `dist(b, B^1) = min_x mu_E{e : b_e != (dx)_e}`. Then
  **`val(b) = 1 - dist(b, B^1)`** exactly.
* A **cycle system** `C` is a probability distribution on closed walks
  `c = (v_0, v_1, ..., v_l = v_0)` of `G` with finite support. The holonomy is
  `hol_b(c) = b_(e_l) ... b_(e_1)`; `c` is **flat** if `hol_b(c) = 1`.
  Flatness does not depend on the base point. `nf_C(b) = mu_C{c : c non-flat}`.
* The **congestion** is `M(C) = max_e m_C(e) / mu_E(e)`, where `m_C(e)` is the
  expected number of traversals of `e` (in either direction) by `c ~ mu_C`.
* The **coboundary expansion** is
  `beta_A(C) = inf { nf_C(b) / dist(b, B^1) : b not in B^1(G; A) }`.
* The **cycle-test cost** is `kappa_A(G, C) = M(C) / beta_A(C)` (`= infinity`
  when `beta_A(C) = 0`).

**Theorem.**

* **(T1) Two-sided bound.** For every cochain `b`,
  `beta_A(C) (1 - val(b)) <= nf_C(b) <= M(C) (1 - val(b))`.
* **(T2) Test.** Given `(G, b)` and a finite explicit `C`, the algorithm
  "accept iff `nf_C(b) <= M(C) eps`" runs in time polynomial in
  `|E| + |supp C| + max length` and decides Gap-Shift`_A[1 - eps, delta]` on
  every instance with `kappa_A(G, C) eps < 1 - delta`. It is uniform in `A`:
  one algorithm serves all groups.
* **(T2') Gate.** Let `f` be a polynomial-time reduction from a language `L`
  to Gap-Shift`[1 - eps, delta]` over groups `A_x`, together with a
  polynomial-time map `x -> C_x` into cycle systems of the output host, such
  that `kappa_(A_x)(G_x, C_x) <= K` for all `x` with `K eps < 1 - delta`. Then
  `L in P`. So under `P != NP` **every UGC route through shift games** (the
  KKMO route to affine UG over `Z_q` or `F_2^N`, and every host-preserving
  route through group-shift games) must output hosts whose cycle-test cost is
  at least `(1 - delta)/eps` for every polynomial-time cycle system, and hence
  unbounded as `eps -> 0`. The step where every member dies is completeness:
  a `1 - eps` YES instance has non-flat mass at most `M eps`, and this is
  already below the NO lower bound `beta (1 - delta)`.
* **(T3) Independence from the spectral invariants.** *Windmill.*
  `W_s(eta)` has apex `a` and `s` triangles `(a, u_i, v_i)`, with
  `mu_E(u_i v_i) = (1 - eta)/s` and `mu_E(a u_i) = mu_E(a v_i) = eta/(2s)`,
  `0 < eta < 2/3`, and `C` uniform on the `s` triangles. For every group `A`,
  `M = 2/eta`, `beta_A = 2/eta` and `kappa_A = 1`, so T2 decides every gap
  `eps < 1 - delta`. Yet `lambda_2(W_s) <= eta/(2 - eta) -> 0`, and at least
  `s - 1` normalized-Laplacian eigenvalues are at most `eta/(2 - eta)`.
  *Converse.* On a graph of girth `> r` with positive cycle rank, every closed
  walk of length `<= r` has trivial holonomy, so `beta = 0` and
  `kappa = infinity` for every `C` of length `<= r`,
  whatever `lambda_2` is (Petersen: `lambda_2 = 2/3`). The two invariants are
  therefore logically independent. The artifact also computes, over `Z_2`,
  `kappa = 2` for `K_4 x K_2` and `kappa ~ 3` for the cone over `K_3 + K_3`
  with apex weight `eta = 0.01`, where `lambda_2 = 0.005`.
* **(T4) Scope: shift games only.** The flatness test fails for general
  unique games. On `K_m` with alphabet `{1, 2, 3}` and every constraint the
  transposition `(2 3)`, the value is `1` (all labels `1`), yet every triangle
  has holonomy `(2 3) != 1`, so `nf = 1`. The host-preserving lift
  `unique-games-lift-to-group-shift-games-on-the-same-host` costs a factor up
  to `k!` in completeness, which destroys the `1 - eps` regime. General UG on
  bounded-`kappa` hosts is left OPEN (survivors below).

**Bearing.** By `ugc-is-equivalent-to-affine-ugc`, UGC is equivalent to
NP-hardness of Gap-Shift over `Z_q`. Via T2', UGC (with `P != NP`) therefore
*implies* that the KKMO output hosts, like every host family that carries
shift-UG hardness, have cycle-test cost `>= (1 - delta)/eps` over `Z_q` for
every polynomial-time cycle system. This is a second necessary shape of hard
YES outputs, independent of `lambda_2 = O(1 - opt)`: hard hosts must be poor
`H^1` testers **and** poor spectral expanders at scale `eps`. Any proposal to
carry shift-UG hardness on a fixed family whose short cycles make `B^1` a
locally testable code (for example the 2-skeleton of a complex with coboundary
expansion over all groups, uniformly in the alphabet) dies at T2.

**What this does not kill.**

* Hosts of large girth relative to the cycle length the test is allowed.
  Every member of the spectral kill's survivor class may still be one.
* General (non-shift) unique games on bounded-`kappa` hosts, T4.
* The known separating examples in T3 are block graphs (a cut vertex at the
  apex), which are easy for elementary reasons as well. A natural 2-connected
  family with `lambda_2 -> 0`, unbounded threshold rank, no global
  hypercontractivity and bounded `kappa`, such as clique trees glued along
  edges, is left OPEN.

**Survivor questions (OPEN).**

1. *Pointed test for general UG.* Is there `beta' > 0` and a cycle
   statistic, for example the mass of cycles whose holonomy has no fixed point
   inside a list of `O(1)` labels chosen at the base, that is at least
   `beta' (1 - val)` on bounded-`kappa` hosts uniformly in `k`?
2. *Evasion cost.* Does some gap-preserving map raise the cycle-test cost of
   every shift-game instance (as the degree-product overlay raises
   `lambda_2`)? Subdivision does not work, because it lifts soundness to
   `>= 2/3`.
