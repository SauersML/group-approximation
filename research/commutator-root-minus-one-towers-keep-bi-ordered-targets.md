---
rg: 2
id: commutator-root-minus-one-towers-keep-bi-ordered-targets
kind: claim
title: The generalized torsion of G(K; -1, 1) only forces the tower letters y_1, y_2, … to alternate in sign, so bi-ordered targets survive on the tower; Bagayoko's hyperseries group receives N_[0,4] with every letter kept, putting N_[0,4] in H for all K, and from N_[0,5] on each extension needs a conjugator of the non-default sign, which exists exactly when an Abel difference is bounded
distinct_from:
  commutator-root-minus-one-groups-have-generalized-torsion: that kills maps of the whole group G(K; -1, 1), where every y_i is a conjugate of y; here the maps are defined only on N_[0,n] and ignore t, so nothing ties the signs of y_1 and y_2, and its identity only says that they are opposite.
  hyperseries-conjugators-put-commutator-roots-in-h: that covers (α, β) = (1, ±1), where each letter keeps one sign. Its item 5 stops the (-1, 1) recursion at N_[0,3] and says the identity kills every bi-orderable target of N_[0,3]. Both are corrected here. The mirror case of its conjugator lemma gives conjugators above x, and the recursion reaches N_[0,4].
  commutator-root-frontier-kills-pl-and-bi-ordered-targets: its item 4 constrains maps of G, which must respect t; without t its local convex rules only force alternation, so it gives no tower obstruction.
  malcev-root-steps-put-commutator-root-one-relators-in-h: its items kill residually-𝒮 targets; the target here is a group of hyperseries, not residually solvable.
  kaplansky-zero-divisor-conjecture: no case of the conjecture changes; torsion-free one-relator groups already satisfy it.
artifacts:
  - experiments/commutator-root-minus-orders-2026-09-19/bo_sat_ns.py
  - experiments/commutator-root-minus-orders-2026-09-19/tower_wp.py
  - experiments/commutator-root-minus-orders-2026-09-19/perms_2_-1_1.txt
  - experiments/commutator-root-minus-orders-2026-09-19/runs.log
---

**ESTABLISHED** (written proof, unreviewed) by [[commutator-root-minus-one-towers-keep-bi-ordered-targets-proof]].
Items 1-3 are proved. Item 4 is a computation. Item 5 is a reduction, and its hypothesis is open. The proof
uses the four stated results of Bagayoko (arXiv:2509.09186) quoted in
[[hyperseries-conjugators-put-commutator-roots-in-h-proof]]. This is a partial step on the 8 open (-1, 1)
words: it removes the claimed obstruction and pushes the tower two levels past it. Nothing is new for the
zero-divisor conjecture.

**Setting.** As in [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]]:
- `G(K; -1, 1) = <y, t | y_1^K = [y_0^{-1}, y_2]>`, with `y_i = t^{-i} y t^i` and `[g, h] = g^{-1} h^{-1} g h`.
- `N` is the normal closure of `y`, and `N_[m,n] = <y_m, …, y_n>`.
- `N_[0,1]` is free on `y_0, y_1`. For `n ≥ 1`, `N_[0,n+1]` is the HNN extension of `N_[0,n]` with stable
  letter `y_{n+1}`, cyclic edge group `<y_{n-1}>` and relation `R_{n-1}`:
  `y_{n+1}^{-1} a y_{n+1} = a y_n^K`, where `a = y_{n-1}^{-1}`.
- `Γ` is Bagayoko's bi-ordered group of positive infinite hyperseries under composition, with identity `x`.
- For a map `φ` into a bi-ordered group, `σ_i ∈ {+, -}` is the sign of `φ(y_i)` when `φ(y_i) ≠ 1`.

## Theorem

1. **Maps into torsion-free groups keep every letter.** Let `φ: N_[0,L] → Q`, with `Q` torsion-free and `L ≥ 2`.
   If `φ(y_m) = 1` for one `m`, then `φ(y_i) = 1` for every `i` with `1 ≤ i ≤ L - 1`. So for `L ≥ 3` a map that
   keeps the edge letter `y_{L-2}` keeps all of `y_0, …, y_L`.
2. **The identity only forces alternation.** Let `φ: N_[0,L] → Q` keep every letter, with `Q` bi-ordered and
   `L ≥ 3`. Then `σ_{j+1} ≠ σ_{j+2}` for `0 ≤ j ≤ L - 3`. So `σ_1, …, σ_{L-1}` alternate. No condition is placed
   on `σ_0` or `σ_L`. The t-invariance that makes this contradictory in `G` is absent on the tower.
3. **Hyperseries tower.** For every `K ≥ 1`:
   - (a) *Extension rule.* A map `φ: N_[0,n] → Γ` keeping `y_{n-1}, y_n` extends to `N_[0,n+1]` if and only if
     `A = φ(y_{n-1})^{-1}` and `B = A φ(y_n)^K` lie on the same side of `x`. Under alternation
     (`σ_{n-1} ≠ σ_n`) this holds automatically.
   - (b) *Default sign.* If `A, B` lie on the same side of `x`, write `(A', B')` for `(A, B)` or `(A^{-1}, B^{-1})`,
     whichever lies above `x`. The conjugators `y_{n+1} ↦ c` are `c_s = V_{A'}^{-1} ∘ (V_{B'} + s)`, `s ∈ ℝ`. Some
     `c_s` has sign `+` iff `B' < A'` or `V_{A'} - V_{B'}` is bounded above by a real. Some `c_s` has sign `-`
     iff `A' < B'` or `V_{A'} - V_{B'}` is bounded below by a real. In sign terms, the sign that always exists
     is the default `σ_{n+1} = σ_{n-1} σ_n`.
   - (c) *N_[0,4] is in H.* There is `φ: N_[0,4] → Γ` keeping every letter, with signs
     `(σ_0, …, σ_4) = (-, -, +, -, -)`, built from default conjugators only. Hence `N_[0,2], N_[0,3], N_[0,4]`,
     and every shift `N_[m,m+4]`, lie in 𝓗.
   - (d) *Hard steps.* Under alternation the default agrees with `σ_{n+1} = -σ_n` iff `σ_{n-1} = -`. So a map
     `N_[0,L] → Γ` keeping `y_{L-2}` uses at least `⌊(L-3)/2⌋` extensions with `(σ_{n-1}, σ_n) = (+, -)`. Each
     one needs `V_{y_{n-1}} - V_{y_n^{-K} y_{n-1}}` (images in `Γ`) bounded above by a real. The first is at
     `L = 5`. No map built from default conjugators alone passes `N_[0,5]`.
4. **Ball test for `G(2; -1, 1)`** (`bo_sat_ns.py`, `runs.log`). The ball is words of length at most `r` in
   `y_0, …, y_{W-1}`, merged by the exact word problem, with the bi-order clauses of
   [[commutator-root-minus-one-groups-have-generalized-torsion]] item 2. It is solved under three rules for `t`:
   - `t`-invariant (a bi-order of `G`): UNSAT at `(W, r) = (3,3), (4,3)`, as that node found.
   - no rule (a bi-order of `N_[0,W-1]`): SAT at `(W, r) = (3,3), (3,4), (4,3), (4,4), (5,3), (5,4), (6,3),
     (7,3)`. The `W = 7` model has signs `(+, +, -, +, -, +, +)`: alternating on `y_1, …, y_5`, and equal at both
     ends, exactly as item 2 allows. The `(5, 4)` model has the signs `(-, -, +, -, -)` of item 3(c).
   - `t`-reversing (`g > 1 ⇔ t^{-1} g t < 1`): SAT at `(3,3), (4,3), (4,4), (5,3), (5,4), (6,3), (7,3)`.
   SAT is only consistency on a finite ball, not an order.
5. **Reduction.** `G(K; -1, 1) ∈ 𝓗` iff `N ∈ 𝓗`. So it follows if `N` is bi-orderable. That holds, for
   example, if `N` has a `t`-reversing bi-order, which is then `t^2`-invariant and bi-orders
   `G_2 = N ⋊ <t^2>`. Item 2 permits such an order, and item 4 finds no finite obstruction to one. Whether `N`,
   or `N_[0,5]`, is bi-orderable is open.

## Consequence for the frontier

The step asked for a target receiving `N_[0,3]` with generalized torsion, or a proof that every 𝓗-target kills
`y`. Neither is needed at `N_[0,3]` or `N_[0,4]`. The bi-ordered group `Γ` works there. The identity cannot
give the second option: by item 2 it is consistent with bi-ordered tower maps at every height.

The next step is item 3(d) at `L = 5`. Choose the free images of `y_0, y_1` and the parameters `s` of the earlier
conjugators so that one Abel difference is bounded. Alternatively, construct a `t`-reversing bi-order of `N`.
