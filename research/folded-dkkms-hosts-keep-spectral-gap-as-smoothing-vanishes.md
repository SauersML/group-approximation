---
rg: 2
id: folded-dkkms-hosts-keep-spectral-gap-as-smoothing-vanishes
kind: claim
title: The folded DKKMS 2-to-1 constraint graph keeps a spectral gap c(l) > 0 that does not depend on the smoothing beta, the tuple size k or the 3LIN source gap, because Lemma 4.1 folding resamples every block that the class representative misses; the unfolded host has gap only Theta(beta)
distinct_from:
  akkstv-rounding-holds-on-all-loop-free-constraint-graphs: that proves the selector gate (G), which needs a host gap; this is the conjectured gap bound for the DKKMS host itself, which is what (G) would need to kill selectors on DKKMS instances.
  efficient-branch-selector-on-proved-2to1-instances: that is the selector hole; this is a spectral statement about the host, with no selector in it.
  dkkms-2to1-instances-satisfy-selector-decoding-hypotheses: that verifies decoding hypotheses of the DKKMS instance; this measures and explains the spectrum of its folded constraint graph.
artifacts:
  - experiments/ugc-akkstv-regularize-2026-09-17/dkkms_folded_gap_large.py
  - experiments/ugc-akkstv-regularize-2026-09-17/dkkms_host_gap.py
---

**OPEN.** Numerics and a mechanism are below. They do not add up to a proof.

*Setting.* The DKKMS instance (TR16-198 Sec 4.2) is used as quoted in
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`:
- a regular 3LIN source;
- legitimate `k`-tuples `U`, with `X_U = F_2^(3k)` and `H_U = span(x_e)`;
- `A = {(U,L) : L ∩ H_U = 0}` and `B = {(V,L')}`;
- smoothing `β`, the probability that a coordinate of `V` is a variable;
- classes `C = {(U,L) : L + H_U = R + H_U}` (Lemma 4.1).

`λ_2` is `1 − σ_2` of the normalized bipartite matrix.

**Claim.** There is `c(l) > 0`, depending on `l` only, such that the following
holds for every regular 3LIN source with `n >= n_0(k, l)` and every
`β in [0, 1]`:

```text
λ_2(G_folded)  >=  c(l).
```

The conjectured value is `c(l) ≈ 1 − sqrt(1 − 4^(−l))`, which is about `4^(−l)/2`.
The unfolded host `G_unfolded` behaves quite differently: it has
`λ_2 = Θ(β)`, and at `β = 0` it is disconnected.

**Why this matters (conditional kill).** Suppose the claim holds, and take the
selector gate (G) of
`akkstv-rounding-holds-on-all-loop-free-constraint-graphs` with
`s = δ`. Then the following holds for every polynomial-time orientation `o` of
DKKMS instances, unless the NP-hard source is in P:

```text
some YES output G  has  1 − val(U_o(G)) > c(l)/X(δ).
```

Here `l` is fixed by `δ` and not by `η`. So `η' −> 0` is impossible. This kills
H1 (`parity-leaking-branch-selectors-reach-near-perfect-completeness`) and every
near-perfect selector on the DKKMS shape. It needs only P != NP, and it does not
look at views, witnesses or certificates.

**Belief change.** The natural forecast was that the DKKMS host gap is `O(β)`.
The outer tuple moves only through variable coordinates, at rate `β`, and DKKMS
takes `β = log log k / k −> 0`. On that forecast the selector gate would give
only a rate floor, and any bound of the form `c(β,k,l) · gap(source)` would
vanish. The forecast is true of `G_unfolded`, but the game lives on
`G_folded`. There, the gap is set by the folding, not by the smoothing or the
source. The numerics at `β = 0`, where the unfolded host is disconnected, show
this directly.

## Mechanism (heuristic)

Take `β = 0` and `l = 1`, so that `B = {U}`. Write the two-step walk
`B → A → class → member → B` on tuples. `L = {0, x}` with `x ∉ H_U`. Reduce
`x` modulo `H_U` to its least-support representative `R`. On each block `e_i`,
`x|_(e_i)` is in `{000, 111}` (reduces to `0`) or reduces to one variable. So
`R` picks at most one variable in each block, and block `i` is **free**
(`R` misses it) with probability `1/4`.

The class of `R` contains `(U', L')` exactly when `U'` covers `supp(R)`, and then
`L' ≡ R mod H_U'`. So the step from `U` to `U'` does two things:
- it resamples every free block uniformly;
- it moves each other block along the equation–variable–equation walk through
  its chosen variable.

For general `l`, block `i` is free iff the projection of `L` to
`F_2^(e_i)/<111> ≅ F_2^2` is zero. That has probability about `4^(−l)`.

Now pretend that legitimate tuples are distributed as a product. Resampling a
random free set `F`, with `P(i in F) >= p` for every block, contracts each
Efron–Stein component `S ≠ ∅` by `P(F ∩ S = ∅) <= 1 − p`. The non-free moves
are positive semidefinite (`M M^T` for the equation–variable incidence), so
they can only help. So the two-step walk has second eigenvalue at most
`1 − 4^(−l)`, and

```text
λ_2 >= 1 − sqrt(1 − 4^(−l))       (l = 1: 0.134,  l = 2: 0.0318,  l = 3: 0.0079).
```

This bound is free of `k`, `n`, `β` and the gap of the source.

## Prerequisites (each can fail)

- **(P1) Classes are least-support fibres.** The Lemma 4.1 class of `(U,L)`
  should be, up to `o(1)` of the mass as `n/k −> ∞`, the fibre of the
  least-support representative `R`. It fails if the paper's partition picks
  representatives that tie `U'` to `U` on more than `supp(R)`.
  Measured `exact-mass`: 0.95–0.97 at `n = 24`, `k = 2`.
- **(P2) Free blocks.** For `L` uniform in `Gr(X_U, l)` with `L ∩ H_U = 0`, each
  block should be free with probability `>= 4^(−l)(1 − o(1))`. This is a
  finite count, and likely routine.
- **(P3) Near-product tuples.** Legitimate tuples should be close enough to a
  product measure for the Efron–Stein contraction to hold up to `o(1)`, for
  example when `n >> k^2`.
- **(P4) Grassmann fibre.** For `l >= 2`, functions of `L'` at fixed `U` must
  also mix. This is the containment walk in `X_U` restricted to `L ∩ H_U = 0`.
  Its gap should be a constant depending on `l` (compare `check_degree_blowup.py`
  Part D for the unrestricted containment host). A decomposition theorem
  (projection chain times fibre chain) would then combine (P3) and (P4).
- **(P5) `β > 0`.** The smoothing adds moves. The gap should not drop below the
  `β = 0` value by more than a constant factor. Numerically it rises with `β`.

If (P1)–(P5) hold, the claim follows with `c(l) = Ω(4^(−l)) · c_fib(l)`.

## Numerics

`dkkms_folded_gap_large.py` builds a random 2-regular 3LIN system on `n`
variables (seed 20260918) and runs the edge process exactly. It reports four
quantities:
- `λ_2` of the unfolded host;
- `λ_2` of the within-`U` folding, which is the finest folding and so a lower
  bound for every Lemma 4.1 folding;
- `λ_2` of the canonical least-support folding;
- the A-mass on which the canonical fibres are exactly the Lemma 4.1 sets.

| n | k | l | β | unfolded | within-U | canonical | exact-mass |
|---|---|---|---|---|---|---|---|
| 24 | 2 | 1 | 0.5 | 0.02665 | 0.02665 | 0.20169 | 0.973 |
| 24 | 2 | 1 | 0.1 | 0.00500 | 0.00500 | 0.18367 | 0.973 |
| 24 | 2 | 1 | 0.02 | 0.00098 | 0.00098 | 0.18021 | 0.973 |
| 24 | 2 | 1 | 0 | 0 | 0 | 0.17936 | 0.973 |
| 24 | 2 | 2 | 0.5 | 0.01940 | 0.02312 | 0.05475 | 0.953 |
| 24 | 2 | 2 | 0.1 | 0.00446 | 0.00457 | 0.03837 | 0.953 |
| 24 | 2 | 2 | 0.02 | 0.00090 | 0.00090 | 0.03509 | 0.953 |
| 24 | 2 | 2 | 0 | 0 | 0 | 0.03427 | 0.953 |
| 30 | 3 | 1 | 0 | 0 | 0 | 0.21881 | 0.936 |

- *Unfolded.* The unfolded gap is linear in `β`: about `0.05 β` here. It is
  exactly `0` at `β = 0`.
- *Canonical folded.* The folded gap converges to a positive constant as
  `β −> 0`. That constant sits just above the mechanism's prediction:
  `0.179 >= 0.134` for `l = 1`, and `0.0343 >= 0.0318` for `l = 2`.
- *Growing k.* Going from `k = 2` to `k = 3` at `l = 1` does not shrink the
  folded gap: it goes from `0.179` to `0.219`.
- *Dense instance.* `dkkms_host_gap.py`, on the dense AG(2,3) instance with
  `k = 2`, `l = 2`, gives the same picture: canonical `0.0995` and `0.0938` at
  `β = 0.1` and `0.02`, while the unfolded values are `0.0035` and `0.00014`.

## Attempts

* **`O(β)` forecast (2026-09-18).** **Refuted for the folded host.** The
  forecast held that the tuple moves only at rate `β`, so the gap is `O(β)`.
  That is true of `G_unfolded`, as the tables show. It ignores the fact that a
  class's members range over every `U'` that covers `supp(R)`.
* **Union-find closure of `L + H_U + H_U' = L'' + H_U + H_U'` (2026-09-18).**
  **Discarded.** This relation is not transitive. Its closure collapses the
  `k = 2` dense instance to a single class, which yields an upper bound only and
  says nothing about the gap. The quoted Lemma 4.1 form, with a single `R` per
  class, is what the canonical fibres implement.
* **Open step.** Prove (P1)–(P5). The quickest route is probably a
  projection/fibre decomposition theorem, with (P2) and (P3) handled by the
  Efron–Stein bound above.
