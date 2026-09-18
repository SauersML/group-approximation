---
rg: 2
id: zn-rips-slack-sphere-criterion
kind: claim
title: The partition criterion for contractible Rips complexes of Z^n extends to scales with unbalanced n-part partitions via slack-one dominators
distinct_from:
  zn-rips-sphere-balanced-dominator-criterion: that criterion needs every partition of r into at most n parts to be balanced, so it fails at every odd r ≤ 35 for n = 7; this one allows unbalanced n-part partitions and replaces Lemma 3 for them by a slack-one dominator plus a finite check against the other unbalanced sphere points
  z6-rips-contractible-at-scales-6-to-9: that is a per-scale certificate over the whole link set Lmax; this is a scale-free test on partitions of r, whose cost does not grow with |Lmax|
---

Notation. `|·| = |·|_1`. A vector `x ∈ Z_{≥1}^s` is **balanced** if some integer `y` with `0 ≤ y ≤ x`,
`y ∉ {0, x}` has `⟨σ,y⟩` between `0` and `⟨σ,x⟩` for every `σ ∈ {±1}^s`. Let `U(n,r)` be the set of
unbalanced partitions of `r` into at most `n` parts.

Call `y ∈ Z^n` a **slack-one dominator** of a positive vector `x ∈ Z_{≥1}^n` at index `k` if:
- `0 ≤ y ≤ x`, `y ∉ {0, x}`, and `y_k ≥ 1`;
- `⟨σ,y⟩ ≤ max(1, ⟨σ,x⟩)` for every `σ ∈ {±1}^n`;
- no `z ∈ Z^n` whose magnitudes `(|z_1|, …, |z_n|)` rearrange to a partition in `U(n,r)` has `z_k > 0`,
  `|z − x| ≤ r` and `|z − y| > r`.

**Theorem.** Let `n ≥ 1` and `r ≥ 2`. Suppose every partition in `U(n,r)` has exactly `n` parts, and every
`x ∈ U(n,r)`, read as a vector, has a slack-one dominator at every index `k`. Then `VR(Z^n, d_1; r)` is contractible.

When `U(n,r)` is empty, this is `zn-rips-sphere-balanced-dominator-criterion`. The hypothesis is a finite check on
partitions of `r`. The route `zn-rips-slack-sphere-criterion-proof` proves the theorem. It keeps that criterion's
peeling and its Stage 2, and it deletes the top sphere in two passes: first the balanced points, then the unbalanced
ones. The slack-one inequality forces every `z` that could break domination onto the top sphere, and after the first
pass the only sphere points left are unbalanced, with full support.

Computed status (`experiments/zn-rips-slack-sphere-2026-09-18/results.txt`):
- `n = 7`: the hypothesis holds at `r = 12, 14, 16` and at every `r` with `18 ≤ r ≤ 54`. At `r = 10, 11, 13, 15, 17`,
  some unbalanced partition has six parts, so the theorem does not apply. See
  `z7-rips-contractible-at-scales-12-14-16-and-18-to-54`.
- `n = 8`: the hypothesis holds at every even `r` with `20 ≤ r ≤ 36` and at every `r` with `37 ≤ r ≤ 70`. See
  `z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70`.
- `n ≤ 6`: the hypothesis holds wherever it applies and was tested (`n = 4`, `r = 5`; `n = 5`, `r = 6, 7, 9`;
  `n = 6`, `r = 8, 10, 11, 13, 15, 17`). Explicit point-level replays on `Lmax` agree.

Limit of the method. At the scales where some unbalanced partition has fewer than `n` parts, deleting the top sphere
first fails, and this does not depend on the slack-one condition. Take `n = 5`, `r = 5`, and let `Lmax` be
`L([−r,r]^{n−1} × [0,r])`. On `Lmax`, 96 of the 176 unbalanced sphere points have no dominator anywhere in
`hull(0,x)` against the current set, whatever the deletion order. At `n = 6`, `r = 6`, the count is 284 of 512. In
every case, the stuck points have a zero coordinate. Rounds of simultaneous deletion give the maximal closure, because domination is monotone in the current
set. The same happens with slack-one dominators at `n = 6`, `r = 6, 7, 9` and at `n = 7`, `r = 10`. So the open
scales for `n = 7` (`10, 11, 13, 15, 17`) need Stage 1 to interleave with lower norms. Checks: `hull_rounds.py` and
`sphere_rounds.cpp`, Section F of `results.txt`.
