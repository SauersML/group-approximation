---
rg: 2
id: thompson-f-standard-normal-forms-not-automatic-proof
kind: route
title: The telescoped normal forms of x_n^-1 and x_n^-1 x1 = x1 x_(n+1)^-1 diverge because z_k = x0^k x1 x0^-k has a deep breakpoint near 0
target: thompson-f-standard-normal-forms-not-automatic
requires: []
artifacts:
  - research/artifacts/guba-sapir-normal-forms-not-automatic-2026-09-16.md
---

Direct proof. The full argument is §7 of the artifact. It uses Lemma A, Lemma C,
(C1) and Lemma D from §2–§4 of the same artifact, which are also summarized in
`thompson-f-guba-sapir-normal-forms-not-automatic-proof`. Notation as in the
target.

**Step 1: the words and the relation.**
- `x_n^-1` and `x_1 x_(n+1)^-1` are standard normal forms. Their only nonzero
  exponents are `c_n = 1`, and `b_1 = 1` with `c_(n+1) = 1`, so the reducedness
  condition is vacuous.
- Their substitutions `s_n` and `t_n` are already freely reduced, so both lie
  in `T`.
- Artifact §1 derives `x_1^-1 x_n x_1 = x_(n+1)` for `n >= 2` from the two
  Cannon–Floyd–Parry relators. It gives `x_n^-1 x_1 = x_1 x_(n+1)^-1`, that is,
  `s_n y = t_n`.

**Step 2: the distance bound.**
- Fix `1 <= k <= n - 1` and put `p = x^-k`, a vertex of `P(s_n)`.
- Put `z_k = x^k y x^-k`. As a PL map, `ρ(z_k)` has a breakpoint at
  `c_k = 2^-(k+1)`.
- The vertices `q` of `P(t_n)` and the corresponding elements `p^-1 q` are as
  follows.

| `q` | `p^-1 q` | bound |
| --- | --- | --- |
| `1` | `x^k` | exponent sum: `>= k` |
| `y x^-j`, `0 <= j <= n` | `z_k x^(k-j)` | exponent sum `>= abs(k - j)`; Lemma C with `f = ρ(z_k)` gives `>= j - 1` for `j >= 1` |
| `y x^-n y^-1 x^j`, `0 <= j <= n` | `z_k x_(n-k+1)^-1 x^(j-n+k)` | exponent sum `>= abs(n - k - j)`; Lemma C with `f_T` and `j' = n - j` gives `>= n - j - 1` for `j <= n - 1` |

In the third row, `f_T = ρ(z_k) ∘ ρ(x_(n-k+1)^-1)`. It keeps the breakpoint
`c_k` by (C1), because `ρ(x_(n-k+1)^-1)` is the identity on `[0, 3/4]`, using
`n - k + 1 >= 2`.

In each case the two bounds sum to `k - 1`, or one bound is at least `k - 1`.
So `|p^-1 q| >= (k - 1)/2` for every vertex `q`. With `k = n - 1`, the vertex
`x^-(n-1)` of `P(s_n)` is at distance at least `(n - 2)/2` from `P(t_n)`.

**Step 3: conclusion.** Lemma D of the artifact says that, in a synchronous or
asynchronous automatic structure over `A`, accepted `u`, `v` with `ū y = v̄`
have paths within bounded Hausdorff distance `K`. Applied to `(s_n, t_n)` for
infinitely many `n`, this contradicts Step 2 for large `n`.

**Trust surface.**
- The CFP presentation.
- The CFP definition of the standard normal form. Only the membership of two
  explicit words in `T` is used; uniqueness of normal forms is not.
- The ECHLPT definitions behind Lemma D.

**Computation.** `experiments/thompson-f-guba-sapir-ftp-2026-09-16/check_tsnf.py`
checks the following in exact arithmetic.
- The relation, for `3 <= n <= 30`.
- The exponent sums and depth bounds at every vertex, for all `k` when
  `n <= 12`, and for `k = n - 1` when `n <= 30`.
- The bound itself.

The output is `TOTAL FAILURES: 0`. The proof does not rely on the computation.
