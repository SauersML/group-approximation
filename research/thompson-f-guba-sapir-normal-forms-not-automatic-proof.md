---
rg: 2
id: thompson-f-guba-sapir-normal-forms-not-automatic-proof
kind: route
title: Breakpoint depth bounds word length, so the Guba–Sapir normal forms of y x^L and y x^L y have Cayley-graph paths at unbounded Hausdorff distance
target: thompson-f-guba-sapir-normal-forms-not-automatic
requires: []
artifacts:
  - research/artifacts/guba-sapir-normal-forms-not-automatic-2026-09-16.md
---

Direct proof. The full argument, with every case, is §1–§6 of the artifact.
Notation as in the target. Words over `A` act as piecewise-linear maps of
`[0,1]`, with `x ↦ X0` and `y ↦ X1` (the standard generators). The word
`s1 ... sk` goes to the composite `s1 ∘ ... ∘ sk`.

**Step 0: a homomorphism, and the relation.**
- Both relators map to the identity, so this gives a homomorphism `ρ` from `F`.
  Every lower bound below is proved by applying `ρ` to an arbitrary word, so
  injectivity of `ρ` is never used.
- Put `x_n = x^-(n-1) y x^(n-1)`. From the two relators one derives
  `x_1^-1 x_n x_1 = x_(n+1)` for `n >= 2`, by induction (artifact §1). This is
  equivalent to `u_L y = v_L`.
- Membership of `u_L` and `v_L` in `N` is read off the definition.

**Step 1: the invariants.**
- `α(h) = log2` of the slope of `ρ(h)` at `0`. It is a homomorphism with
  `α(x) = -1` and `α(y) = 0`, so `|h| >= |α(h)|`.
- *Lemma A.* `|h| >= D(ρ(h)) - 2`, where `D` is the largest dyadic depth of a
  breakpoint. The proof: `bp(f∘g) ⊆ bp(g) ∪ g^-1(bp(f))`. Each generator has
  breakpoints of depth at most `3` and is piecewise `t ↦ 2^e t + d` with
  `|e| <= 1` and `d ∈ (1/8)Z`. So each letter raises `D` by at most `1`.

**Step 2: breakpoints that survive composition.**
- If `g` is linear near `t` and `g(t) ∈ bp(f)`, then `t ∈ bp(f∘g)`. If
  `t ∈ bp(g)` and `f` is linear near `g(t)`, then `t ∈ bp(f∘g)`.
- `ρ(x_(a+1)^-1)` has a breakpoint at `1 - 2^-(a+1)`.
- `ρ(z_m)`, with `z_m = x^m y x^-m`, has a breakpoint at `c_m = 2^-(m+1)`.
- Pulling these back through `X0^k`, which is linear near the relevant dyadic
  points, gives the following (artifact §3).
  - *Lemma B.* `D(ρ(x_(a+1)^-1 x^(j-a))) >= j + 1` for `a, j >= 1`.
  - *Lemma C.* If `c_m ∈ bp(f)`, then `D(f ∘ X0^(m-j)) >= j + 1` for `j >= 1`.
- Lemma C applies to `f_B = ρ(x_(a+1)^-1 z_m)` and to
  `f_C = ρ(x_(a+1)^-1 z_m x_(a+2))`.

**Step 3: the distance bound.** Take `L >= 2`, `a = floor(L/2)`, `m = L - a`
and `p = y x^a`, a vertex of the path of `u_L`. The prefixes `q` of `v_L` fall
into three segments, and for each one `p^-1 q` is an explicit word (artifact §5).

| Segment | `q` | `p^-1 q` | bounds used |
| --- | --- | --- | --- |
| A | `x^j` | `x_(a+1)^-1 x^(j-a)` | `α` and Lemma B |
| B | `x^L y x^-j` | `x_(a+1)^-1 z_m x^(m-j)` | `α` and Lemma C with `f_B` |
| C | `x^L y x^-(L+1) y x^j` | `x_(a+1)^-1 z_m x_(a+2) x^(j-a-1)` | `α` and Lemma C with `f_C`, `j' = L + 1 - j` |

At each vertex, either two lower bounds summing to `a - 1` or `m - 1` apply,
or a single bound of size at least `m - 1 >= a - 1` does. Since `a <= m`, this
gives `|p^-1 q| >= (a - 1)/2`. So `dist(y x^a, P(v_L)) >= (a - 1)/2`.

**Step 4: automatic structures force bounded Hausdorff distance (Lemma D).**
- Let `M_y` be the two-tape automaton of a synchronous or asynchronous
  automatic structure, which accepts the pairs `(u, v)` of accepted words with
  `ū y = v̄`.
- Follow an accepting run up to any moment. Then complete it along a fixed
  shortest path to an accepting vertex in the finite graph of states, where
  end-of-tape flags are recorded in the asynchronous case.
- The completion gives an accepted pair. So the current positions `u(t)` and
  `v(t')` differ by a word of length at most `2|V_y| + 1`.
- Every `t` occurs with some `t'`, and every `t'` with some `t`. So the paths
  are within Hausdorff distance `K`.

**Conclusion.** If `L_0` contained `u_L, v_L` for infinitely many `L`, Step 3
would contradict Step 4 for large `L`.

**Trust surface.**
- The definition of `N`, taken from CGHJS arXiv:1811.11691v1 Section 1, fetched
  2026-09-16.
- The Cannon–Floyd–Parry presentation of `F`.
- The ECHLPT definitions of synchronous and asynchronous automatic structures.
  Lemma D is proved from them in the artifact.

Nothing else is imported.

**Computation.** Exact rational arithmetic checks each convention, identity and
depth claim, and the final bound for `L <= 30`. Exact distances for `L <= 15`
show the bound is not sharp: the true distance is `a + 1`. The scripts and
outputs are in `experiments/thompson-f-guba-sapir-ftp-2026-09-16/`. The proof
does not rely on them.
