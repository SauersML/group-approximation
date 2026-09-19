---
rg: 2
id: rips-segev-port-cycle-counting-has-n-independent-ceiling-proof
kind: route
title: The window criterion is capped by girth at E* <= 39 while it asks for 2N, so for large N a single relator face with L_0 boundary b-edges passes every check of the counting method; any closing active-coset bound must then be below L_0, independent of N
target: rips-segev-port-cycle-counting-has-n-independent-ceiling
requires: [rips-segev-nine-copy-configurations-carry-no-zero-divisors, rips-segev-eight-copy-configurations-carry-no-zero-divisors, rips-segev-support-method-threshold-is-exactly-q-gamma]
artifacts: [experiments/rips-segev-counting-ceiling-2026-09-17/counting_ceiling.py]
---

**Conventions.**  [8C] is `rips-segev-eight-copy-no-zero-divisors-proof` and [9C] is
`rips-segev-nine-copy-no-zero-divisors-proof`.  Windows, `n*`, `e*`, `E*` and (H_N) are as in [8C] §2:
- `n*` is the number of `b`-syllables a window meets, partial ends included;
- `e*` is the number of whole `b^{±2}`-syllables inside it;
- `E* = n* + e*` is its number of `b`-edges.

The cap `E* <= 39` in [8C] Lemma 3 is forced: [8C] Lemma 2 needs the walk-plus-run cycle of length
`<= E* + 2` to be shorter than `girth(Phi) >= 42`.  Nothing in the method lifts it.

## 1. The criterion is capped

**Lemma 1.**  For every window, `n* + max(0, e* - N) = E* - min(e*, N) <= E*`.  So over windows with
`E* <= 39` the maximum is at most `39`.  For `N >= 20` it is below `2N`, and no window of any face of any `D`
meets the criterion.

*Proof.*  Substitute `n* = E* - e*`: `n* + max(0, e* - N) = E* - e* + max(0, e* - N) = E* - min(e*, N)`. ∎

**Lemma 2 (all-`b^2` faces).**  Suppose every `b`-syllable of a face is `b^2`.  Then over windows of its arcs
with `E* <= 39` the maximum of `n* + max(0, e* - N)` is `20 + max(0, 19 - N)`.  It is `>= 2N` exactly when
`N <= 13`.

*Proof.*  Let `p <= 2` be the number of partly covered end syllables.  Every other syllable met is a whole `b^2`,
so `e* = n* - p` and `E* = 2 n* - p`.
- `p = 0`: `n* <= 19` and `e* = n*`.
- `p = 1`: `n* <= 20` and `e* = n* - 1 <= 19`.
- `p = 2`: `n* <= 20` and `e* <= 18`.

The largest value is at `(n*, e*) = (20, 19)`, giving `20 + max(0, 19 - N)`.  For `N <= 13` this is `39 - N`,
and `39 - N >= 2N` iff `N <= 13`.  For `N >= 14` it is at most `25 < 28 <= 2N`. ∎

`counting_ceiling.py` checks Lemma 1 over all window types for `N <= 25`.  It checks Lemma 2 both over window
types and by brute force on every cyclic window of the 21-syllable all-`b^2` face.

## 2. A one-face port-cycle diagram survives

**Lemma 3.**  Let `c` be a directed cycle of `Phi`, of length `m`.
- Its lift to `Gamma` is a closed path.  Its label `r` is positive in `b`, with `m` letters `b`, and is a relator
  of `K`.
- The cyclic reduction of `r` is nontrivial in `<a> * <b>`.  It has a minimal diagram with exactly one face,
  whose boundary is `r` and carries `L = m` `b`-edges.

*Proof.*
- Each `b`-edge of `Gamma` projects to an oriented edge of `Phi`.  Between two consecutive edges of `c` at a
  vertex `v_l`, the lift runs along the `a`-line of `v_l`, from the landing position to the departure position.
  So the lift closes up, and its label is `r`, a relator of the graphical presentation of `K`.
- `r` is positive in `b`, so it is nontrivial in `<a> * <b>` ([9C] §5, calibration).  Cyclic reduction only
  merges `b b` into `b^2` ([9C] Lemma 1(a)).  A single relator face is a diagram for it, and a minimal one has at
  least one face. ∎

Every finite digraph with all out-degrees positive has a directed cycle, and each vertex of `Phi` has out-edges
`x_1, ..., x_4`.  So `L_0(Phi)`, the least length of a directed cycle, is finite, with `L_0(Phi) >= 42` by girth.

**The `gamma = 42` graph.**  Item 12 of the target uses `Phi = Cay(Q, {x_1, ..., x_4})` for a finite quotient `Q`
of `<x | (x_4 x_1)^21>`.  There `c = (x_4 x_1)^21` is a directed cycle of length 42.  By the Steenbock table:
- `x_4` lands at position `0`, and `x_1` departs from position `0`.  So `x_4 x_1` reads `b^2`.
- `x_1` lands at `I1 = 10^{5r-4}` and `x_4` departs from `O2 = 10^{5r'-1}`.  The exponents differ mod 5, so
  `I1 != O2`, and the `a`-syllable between them is nonzero.
- So `r` has `l = 42` syllables, alternating `b^2` and `a^{n_j}` with `n_j != 0`, and `L = 42`.  This is the
  extremal face of [8C] Lemma 1(b), with every `b`-syllable `b^2`.

## 3. The method cannot exclude it

Take `W' = r` from Lemma 3, and `D` its one-face diagram.
- *Windows.*  For `N >= 20` Lemma 1 excludes nothing.  For the `gamma = 42` face Lemma 2 excludes nothing once
  `N >= 14`.
- *Curvature.*  [9C] Corollary 4 applies only to diagrams with at least two faces.  With one face it gives
  nothing, and [9C] handles this case by a window alone ([9C] §3, "Diagrams with one face").
- *Face shape.*  [8C] Lemma 1 holds: `l = 42` and all `b`-syllables are `b^2`.
- *Counting.*  The port cycle has `L = m` active cosets.  The only remaining check is `m <= A(N)`.

So in this range the method derives (H_N)-impossibility only if `A(N) < m` for every admissible `m`, that is
`A(N) < L_0(Phi)`.  On the `gamma = 42` graph that means `A(N) < 42`.  Every bound of the form `cN + d` with
`c > 0` fails this for all `N >= (L_0 - d)/c`.  Proven bounds ([3C]: `N + 3N(N-1)/2`) and the one the brief
proposed (`O(1)` dirty cosets per copy) both grow with `N`.  This proves the claim's (a)-(d). ∎

*(e).*  [9C] Lemma 6 bounds shell lengths (`42 <= l <= 54` at `N = 9`) using a window on long shells.  By
Lemma 1 that step disappears at `N = 20`.  Without it, shells of any length survive, and the per-shell bound of
`b`-edges is a constant fixed by `l >= 42` and `C'(1/8)`, not a multiple of `N`.

## 4. Checks

- *Calibration against [9C].*  At `N = 9` Lemma 2 gives `20 + 10 = 30 >= 18`.  So the all-`b^2` face is excluded
  there, as [9C] Lemma 6 says.  At `N = 13` it is still excluded (`26 >= 26`), and at `N = 14` it is not.
- *Scope.*  This is about the method, not about (H_N).  It does not say that such a port cycle exists in a real
  counterexample.  It says the four ingredients cannot rule one out, so no refinement of `A(N)` alone reaches every
  `N`.
- *Larger girth.*  If `girth(Phi) = g > 42`, [8C] Lemma 2 allows windows with `E* <= g - 3`.  Lemma 1 then makes
  the criterion vacuous for `2N > g - 3`, and Lemma 3 still gives a surviving face with `L_0(Phi) >= g` `b`-edges.
  The thresholds move with `Phi`, but for fixed `Phi` they are constants.  The conclusion is unchanged: for all
  large `N` a closing bound must be `A(N) < L_0(Phi)`.
- *What survives.*  For `10 <= N <= 19` windows still bite, and a sharper `A(N)` could close some of that band.
  With `A(N) = (1 + k) N` and `k >= 1` this gives at most `N <= 20`.
- *The next step.*  A single face `M` must be excluded without counting across the covering.
  - Its arc runs through at least 21 consecutive arc cosets of `C_M`, all `b^2` in the extremal case.
  - At most one is pure ([3C] Corollary 2).
  - A coefficient lemma is needed: the port equations `X(zb) = -Y(z)` with fixed ratio `u/w` cannot hold along such
    a run of impure cosets.
  - `rips-segev-coefficient-free-extremal-copy-lemma-fails` shows that supports alone cannot do it.
