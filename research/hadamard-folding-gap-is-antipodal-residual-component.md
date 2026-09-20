---
rg: 2
id: hadamard-folding-gap-is-antipodal-residual-component
kind: claim
title: The Hadamard folding gap is exactly 2-SAT unsatisfiability of a residual graph - for a symmetric weighting the folded pinned min cut equals the relaxed one iff no point shares a strongly connected component with its antipode, and every odd-walk (metric LP) certificate of true soundness caps the deletion ratio at 2
distinct_from:
  hadamard-crossing-needs-folding-gap: that bounds the folding gap above by the edge mass eta_k of the non-folded locus of one optimal relaxed adversary; this characterizes, per weighting and pattern, exactly when the gap vanishes (a 2-SAT/skew-symmetric criterion on a max-flow residual graph) and caps the natural LP strengthening of the relaxation that adds all antipodal walks.
  hadamard-gadget-deletion-ratio-window: that imports Martinsson's cap on the unfolded relaxation; this proves the same cap 2 for the strictly stronger odd-walk LP of the folded problem, so metric certificates cannot cross either.
  hadamard-gadget-crosses-padding-line: that is the open crossing statement; this gives two necessary conditions for it.
---

**ESTABLISHED.** All items are proved in full in
`hadamard-folding-gap-is-antipodal-residual-component-proof`, from the
minimax identity (item 1 of `hadamard-gadget-deletion-ratio-window`),
elementary max-flow theory and the Aspvall-Plass-Tarjan 2-SAT theorem.
Items 1-3 and 4(b) are self-contained. Item 4(a) also uses Martinsson's
relaxed cap, already imported as item 5 of the window claim.

## Setting

Notation of `hadamard-gadget-deletion-ratio-window`: `K = 2^k`,
`Q = {-1,1}^K`, primaries `chi_a` (`a in F_2^k`), length-one edges.

* A *weighting* `w` is a probability measure on length-one edges. It is
  *symmetric* if `w(e) = w(-e)`.
* For a pattern `xi in {-1,1}^K` put `S+ = {xi_a chi_a}` and `S- = -S+`.
* `F(w, xi)`: least `w`-mass cut by a folded `f` (`f(-x) = -f(x)`) with
  `f(chi_a) = xi_a`. This is the true (folded) soundness.
* `M(w, xi)`: least `w`-mass cut by any `f` with `f = +1` on `S+` and
  `f = -1` on `S-`. This is an `S+`-`S-` min cut, Wiman/Martinsson's
  relaxation.
* Minimax (item 1 of the window claim, with `xi` uniform):
  `R*(k) = K max_w E_xi F(w, xi)` and `K z_U(k) = K max_w E_xi M(w, xi)`.

## Theorem

1. **Symmetric weightings suffice.** Both maxima are attained at symmetric
   `w`. In fact `F(w, xi) = F(w^s, xi)` for `w^s = (w + w^-)/2`, and
   `M(w^s, xi) >= M(w, xi)`.
2. **2-SAT criterion.** Let `w` be symmetric and `xi` a pattern. Then
   `F(w, xi) >= M(w, xi)`, and there is a maximum `S+`-`S-` flow `phi`
   invariant under `x -> -x` with arcs reversed. Let `G_phi` be its
   residual graph, with a super-source `s` joined to `S+` and a super-sink
   `t = -s` joined to `S-`. Then
   `F(w, xi) = M(w, xi)` **iff** no vertex `x` of `Q` lies in the same
   strongly connected component of `G_phi` as `-x`.
   * The residual graph is skew-symmetric: `u -> v` is a residual arc iff
     `-v -> -u` is. Folded min cuts are exactly the satisfying assignments
     of the 2-SAT instance whose implication graph is `G_phi` with
     `neg x := -x`.
3. **Odd-walk LP cap.** Let `L(w, xi)` be the value of the LP relaxation of
   `F(w, xi)` that asks for edge lengths `d(e) in [0, 1]` summing to at
   least `1` along every walk from `S+` to `S-` **and** along every walk
   from any `x` to `-x`. Then `M(w, xi) <= L(w, xi) <= F(w, xi)` and
   `L(w, xi) <= 2/K`. So `K max_w E_xi L(w, xi) <= 2`.
4. **Necessary conditions for a crossing.** If `R*(k) > 2`, then for every
   symmetric `w` with `K E_xi F(w, xi) > 2`:
   * (a) with positive probability over `xi`, the symmetric residual graph
     `G_phi(w, xi)` has an antipodal strongly connected component (a
     component `C = -C`);
   * (b) `E_xi [F - L] > (2 - K E_xi L)/K >= 0`, so the certificate of
     `F` must be non-metric. Every lower bound on true soundness obtained
     by packing odd walks (cycles of the signed quotient graph on `Q/±`),
     that is every feasible dual of the odd-walk LP, certifies at most 2.

## What this changes

* **The class that dies.** Odd-cycle / metric-LP certificates of true
  Hadamard soundness. The invariant is walk length: every walk the LP must
  cut has at least `K/2` edges (`d(xi_a chi_a, -xi_b chi_b) = K/2` for
  `a != b`, `K` for `a = b`, and `d(x, -x) = K`). A packing of total weight
  `1` then has value at most `2/K`. This holds at every `k`, so no metric
  argument proves `hadamard-gadget-crosses-padding-line`, at any arity.
  Crossing needs integrality: Sherali-Adams / SDP levels or a direct
  combinatorial count on odd functions.
* **Where the gap lives.** The folding gap `R*(k) - K z_U(k)` is supported
  on patterns whose residual graph links some `x` to `-x` in both
  directions, that is, whose relaxed min cuts can all be uncrossed only by
  breaking antipodal symmetry. This turns `eta_k` of
  `hadamard-crossing-needs-folding-gap` into a checkable, polynomial-time
  test per `(w, xi)` (one max flow plus Tarjan), usable in any census.
