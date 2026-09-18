---
rg: 2
id: rips-segev-two-copy-configurations-carry-no-zero-divisors
kind: claim
title: In Steenbock's Rips--Segev core no relation alpha (u(a) + w(a) b) = 0 with alpha, w != 0 has alpha u and alpha w supported on the union of two translates of g(V(Gamma)), because two translates meet in one bridge or in at most three cosets joined by shared b-runs, so at most five cosets are active and they close a positive relation of length at most 10
distinct_from:
  rips-segev-one-copy-configurations-carry-no-zero-divisors: that handles supports inside one translate h g(V(Gamma)); this handles supports spread over two distinct translates glued along pieces, and re-proves the one-copy case as the degenerate instance.
  rips-segev-witness-supports-carry-no-zero-divisors: that handles beta = p + x a + y b + z ab with alpha on the a-lines; this handles u(a) + w(a) b with the hypothesis on the products alpha u, alpha w over two copies.
  rips-segev-support-method-threshold-is-exactly-q-gamma: that is the support-only threshold q(gamma); this is a coefficient argument valid for every support size, but only for configurations inside two copies of Gamma.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all of k[G(Gamma)]; this excludes two-layer relations inside two translates and reduces three translates to one flank lemma.
artifacts:
  - experiments/rips-segev-two-copy-2026-09-18/two_copy_ports.py
  - experiments/rips-segev-two-copy-2026-09-18/ports_results.txt
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-two-copy-configurations-carry-no-zero-divisors-proof`.

**Setting.**  As in `rips-segev-one-copy-configurations-carry-no-zero-divisors`: `Gamma` is Steenbock's graph
with `Gr'_*(1/8)`, `gamma >= 41`, `K` its core, `G = G_1 *_{<a>} K *_{<b>} G_2`, and `g : V(Gamma) -> K`.  A
*copy* is `h g(Gamma)` in the Cayley graph of `K`, with vertex set `V_h = h g(V(Gamma))`.

**Theorem.**  Let `k` be a field, `u, w in k[<a>]`, `alpha in k[K]`, with `alpha != 0`, `w != 0` and
`alpha (u + w b) = 0`.  Then there are no `h_1, h_2 in K` with
`supp(alpha u) ∪ supp(alpha w) ⊆ V_{h_1} ∪ V_{h_2}`.  The same holds in `k[G]` with `h_1, h_2 in G`.

**Mechanism.**
1. *Two-link lemma.*  If two copies are linked twice (by elements differing by a power of `a` or `b`), the
   van Kampen diagram between the two links has no faces.  An exterior arc of a face meets the two copy paths in
   at most three pieces, so every face would have boundary length `< 8 < gamma`.
2. *Gluing.*  Consequently a `b`-edge bridge between the copies is their only link (first-letter argument).
   Without a bridge, the cosets shared by both copies are pairwise joined by `b`-runs lying in both copies.  By
   rigidity no longer common path exists, and `girth(Phi) > 12` bounds the shared cosets by 3.
3. *Ports.*  Every edge at a port is a copy edge or the bridge.  On a *clean* coset (not shared, no bridge
   endpoint) the one-copy port constraints hold verbatim.
4. *One clean line per copy.*  Two clean active lines in one copy force, by `P_i Q_j = P_j Q_i` and row
   separation, ports at `{0, C}` only.  The `x_1`/`x_4` gluing then makes the two flanking lines active and
   dirty.  They are distinct, and both meet the same copy.  That is impossible with one bridge, and without a
   bridge the shared run joining them closes a cycle of length `<= 4` in `Phi`.
5. *Short relation.*  So at most 5 cosets are active.  Every active coset sends a `b`-edge to an active coset, so
   a directed cycle gives `b a^{n_0} ... b a^{n_{L-1}} = 1` in `K` with `L <= 5`.  This word is nontrivial in
   `F`, and the graphical small cancellation lemma forbids relations of free-product length `<= 24`.

**Scope.**
- The one-copy theorem is the degenerate case: no dirty cosets, so one active coset and the relation `b a^n = 1`.
- **Three or more copies are open.**  The only gap for three copies is a *mixed flank*: the two flanking lines
  of a clean line are dirty through two different copies.  Pairwise lemmas say nothing there.  If mixed flanks
  are excluded, at most `3 + 9 = 12` cosets are active and `2·12 = 24 < 5 gamma/8 - 1` still closes the argument.
- For `N >= 4` copies, the active-coset bound exceeds 12 and the short-relation ending fails.
- Every finite relation lies in finitely many copies, since the copies cover `K`.  So the `N`-copy theorem for
  all `N` is the full `b`-degree-one case of `rips-segev-groups-satisfy-kaplansky-zero-divisor`.

**Calibration.**  `two_copy_ports.py` builds two copies of a 6-line model with separated rows and solves the
coupled port system by exhaustive search over `F_2` and `F_3`.
- It covers the disjoint, bridge, shared-coset, shared-`b`-edge and shared-`2`-run gluings.
- Every allowed gluing has no solution, and neither do the gluings the lemmas exclude.
- The degenerate control (all lines on one position set) has solutions.
- The model graph has short cycles, so it tests the port algebra, not Lemma 6.
