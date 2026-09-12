---
rg: 2
id: numeric-window-relations-do-not-force-balance-proof
kind: route
title: Følner entropy count for amenable decoders, and merge and AND measures with small interiors for nonamenable ones
target: numeric-window-relations-do-not-force-balance
requires: []
artifacts:
  - research/artifacts/numeric-window-relations-no-go-2026-09-12.md
  - research/artifacts/gk-vf-positive-b-verification-2026-09-12.md
---

A complete direct proof is in the artifact.

- **Amenable case (Proposition 1).**
  - Along right Følner sets `F_k` of the decoder memory group, `|F_k \ int_N F_k| = o(|F_k|)`.
  - R3 bounds every pattern probability on `F_k` by `q^(-|int_N F_k|)`, so the Shannon entropy on `F_k` is at
    least `|int_N F_k| log q`.
  - Subadditivity bounds that entropy by `|F_k|` times the site entropy. So the site entropy is `log q`, and
    the site law is uniform.
- **Nonamenable interiors (Lemma 2).**
  - Følner's criterion gives `|FN| >= (1 + eps)|F|` on the subgroup, and then on all of `G` coset by coset.
  - Since `int_N E` times `N` lies in `E`, `|int_N E| <= |E|/(1 + eps)`.
- **Merge measure (Theorem 3).**
  - The rule `f(a_2) = a_1` gives an iid measure with atoms `2/q`, `0` and `1/q`.
  - The counts `q^(|EM|-|E|) 2^#{p = a_1}` are integers, and `{x(e) = a_2}` is null.
  - `nu[p]_E <= (2/q)^|E| <= q^(-theta_N|E|) <= q^(-|int_N E|)` once `q^(1-theta_N) >= 2`.
- **AND measure (Proposition 4).**
  - Transfer matrices `T_0 = [[1,1],[1,0]]` and `T_1 = [[0,0],[0,1]]` bound each run of `l` sites on a coset
    of `<c>` by `(phi_g/2)^l`, where `phi_g` is the golden ratio. Runs and cosets are independent, so
    `nu[p]_E <= 2^(-0.3057|E|)`.
  - In the 4-regular tree, degree counting in the induced forest gives `|int_(B_1) C| <= |C|/3`, hence
    `|int_(B_2) C| <= |C|/9`.
  - Splitting along cosets of the free pair gives `|int_N E| <= |E|/9`.
  - The pattern `(1,0,1)` along `c` is null.
- **Projection measure (Theorem 6).**
  - For `q = r^k`, send the last of the `k` coordinates to a fixed symbol. The result is iid, uniform on
    `r^(k-1)` symbols.
  - Its support is a full shift on those symbols, and the measure is that shift's unique uniform Gibbs
    measure.
  - Completion counts are `r^((k-1)|E|)`. Lemma 2 for `M^-1` gives `k|I_E| <= (k-1)|E|`, so the counts are
    divisible by `q^|I_E|`.
  - R3 holds: `r^(-(k-1)|E|) = q^(-(1-1/k)|E|) <= q^(-|int_N E|)`.

**Verification.** `w4-vf-positive-b` passed this route in Section 3 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`.
- Every step was re-derived.
- There are two wording points: the title's "exactly when", and the tree `distinct_from`.
- At `q = 4`, with decoder memory containing a free radius-2 ball, the merge measure also satisfies both pushforward relations
  (Section 3.6).
- Theorem 6, the projection measure, passes in Section 3.8. I checked G1–G4, the bridge bound `N_Y(E, c) <= q^|E N^-1|`, and the
  entropy identity (4).
- The rows of the Section 5 squeeze pass, but its "must" sentences are a heuristic, not a theorem (Section 3.9).
