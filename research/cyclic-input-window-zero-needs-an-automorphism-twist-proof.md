---
rg: 2
id: cyclic-input-window-zero-needs-an-automorphism-twist-proof
kind: route
title: Along the shift ray, cycle lengths are monotone and line coordinates scale by k, while each value is taken infinitely often
target: cyclic-input-window-zero-needs-an-automorphism-twist
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

Fix `|k| >= 2`. In case (−), `s alpha = alpha^k s` near infinity, so `s` is a near-equivariant partial bijection from the `Z`-set `(N, alpha)` to the `Z`-set `(N, alpha^k)`. In case (+), `alpha s = s alpha^k`, so `s` goes from `(N, alpha^k)` to `(N, alpha)`. Let `E` be the finite set where the relation or the domain fails.

Write `Cyc` for the union of the finite `alpha`-cycles and `Lin` for the union of the infinite `alpha`-orbits (lines). The same sets are the finite and infinite orbits of `alpha^k`, since `k != 0`. For a point `x` in a finite cycle, let `lambda(x)` be the length of its `alpha`-cycle.

## Step 0: one of the two parts is finite

- A near-equivariant partial bijection maps finite orbits near onto finite orbits, and infinite ones near onto infinite ones: see Lemma S of `fw-inputs-pass-window-zero-only-via-proper-self-embeddings-proof`, which does not use FW.
- So `Cyc + 1 = Cyc` up to a finite set, and a subset of `N` that is near-invariant under `+1` is finite or cofinite.
- If `Cyc` is cofinite, then `Lin` is finite. It is a union of infinite orbits, so `Lin = ∅`: this is Case I. Otherwise `Cyc` is finite and `Lin` is cofinite: this is Case II.

## Case I: every orbit is a finite cycle

**Monotonicity.** Let `C` be a cycle avoiding `E`.
- In (−), `s` conjugates `alpha|C` to `alpha^k|s(C)`, so `s(C)` is one `alpha^k`-cycle of length `ℓ = |C|`.
- That `alpha^k`-cycle lies in an `alpha`-cycle of length `ℓ'` with `ℓ = ℓ'/gcd(ℓ',k)`. So `lambda(s x) >= lambda(x)`.
- In (+) the same reasoning gives `lambda(s y) = ℓ'/gcd(ℓ',k) <= lambda(y)`.
- Beyond a position `p_0` exceeding `E` and the finitely many cycles meeting it, `lambda` is therefore monotone along the ray `p ↦ p+1`: non-decreasing in (−), non-increasing in (+).

**Eventually constant is impossible.** If `lambda` were eventually constant, say `ℓ_0`, then `alpha^(ℓ_0)` would fix every large position. It would be finitary, contradicting infinite support. This disposes of (+), where a non-increasing sequence of positive integers is eventually constant.

**Case (−).** Here `lambda` is non-decreasing and unbounded on `[p_0, ∞)`.
- Choose `ℓ >= 2` with `ℓ = lambda(p)` for some `p >= p_0` and `ℓ` larger than every value of `lambda` on `[0, p_0)`.
- The positions with `lambda = ℓ` then form a finite interval of the ray inside `[p_0, ∞)`. Let `z` be its last element and `C_z` the cycle of `z`.
- `s` maps `C_z` into a single `alpha`-cycle `C'`. That cycle contains `z+1`, so `lambda(C') > ℓ`.
- Take `w ∈ C_z` with `w < z`, which exists because `|C_z| = ℓ >= 2`. Then `lambda(w+1) = lambda(C') > ℓ`, while `lambda(z) = ℓ` and `lambda` is non-decreasing on `[w+1, z]`. Contradiction.

## Case II: finitely many cycle points

**Ends.** Each line has a `+` end and a `−` end with respect to the generator.
- A near-equivariant partial bijection maps each end of the source equivariantly onto an end of the target. This gives a bijection between the sets of `+` ends: all but finitely many points lie on the two tails of lines, tails are mapped along the generator, injectivity prevents two ends from sharing a target end, and near-surjectivity hits every target end.
- Suppose `alpha` has `r` lines. Then `alpha^k` has `|k| r` lines, because each `alpha`-line splits into `|k|` residue classes.
- In both cases `r = |k| r` as cardinals, so `r` is infinite, as it cannot be `0`.

**Coordinates.** On each `alpha`-line fix a base point and the coordinate `kappa` with `kappa(alpha x) = kappa(x) + 1`. Every line has exactly one point of each coordinate, so for every integer `v` infinitely many points have `kappa = v`.

In (−), `s` maps a line avoiding `E` into one line, and the two ends of each of the finitely many lines meeting `E` each go into one line, with

    kappa(s x) = k kappa(x) + c,

where `c` depends only on the line, or on the end.

In (+), each `alpha^k`-line maps onto one `alpha`-line, with

    kappa(s x) = kappa(x)/k + d,

where `d` depends only on the `alpha^k`-line.

**Bounded offsets.** Rebasing a line by `q ∈ Z` changes each offset attached to it by a known amount: `k q` or `q/k` on one side, and `−q` on the other. Each offset constraint links a line to one target line (in (−)) or to one parent line (in (+)), so the constraints form a functional graph.
- Choose the `q` backwards along each tree of that graph by rounding. This makes the offsets `O(|k|)`.
- On each cycle of the graph the composite rebasing is an affine map of slope `k^(±n)`. Choosing the rebasing of one vertex suitably keeps its offset within `|k| + 1`.
- The finitely many lines meeting `E` contribute finitely many further offsets.
- So there is `B` with `|kappa(s x) - k kappa(x)| <= B` in (−), and `|kappa(s x) - kappa(x)/k| <= B` in (+), for every `x` outside a finite set `F_0`. The set `F_0` contains the cycle points, `E`, and the middle parts of the lines meeting `E`.

**The ray argument.** Take `p_0 > max F_0`.

(−) Put `M = B + 1`.
- If `p >= p_0` and `|kappa(p)| >= M`, then `|kappa(p+1)| >= 2|kappa(p)| - B >= |kappa(p)| + 1`. So once the ray reaches `|kappa| >= M`, `|kappa|` increases strictly forever, and each value is taken at most once afterwards.
- If the ray never reaches `|kappa| >= M` beyond `p_0`, all the infinitely many points with `kappa = M` lie before `p_0`: impossible.
- Otherwise, each value `v` with `|v| >= M` is taken at only finitely many positions, yet by infinitely many points: impossible.

(+) Put `M = 2B + 1`.
- If `p >= p_0`, then `|kappa(p+1)| <= |kappa(p)|/2 + B`. So the ray enters `|kappa| <= M` after finitely many steps and never leaves it.
- The infinitely many points with `|kappa| > M` must then all occur at finitely many positions: impossible. `∎`
