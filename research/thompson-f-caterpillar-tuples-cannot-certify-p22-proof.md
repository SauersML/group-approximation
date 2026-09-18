---
rg: 2
id: thompson-f-caterpillar-tuples-cannot-certify-p22-proof
kind: route
title: Split by tails, discharge each image's unit weight evenly over its class-preimages, and check that the resulting local sum depends only on four-valued root types
target: thompson-f-caterpillar-tuples-cannot-certify-p22
requires: []
artifacts:
  - experiments/thompson-f-p22-skeleton-2026-09-17/types_check.py
  - experiments/thompson-f-p22-skeleton-2026-09-17/skeleton.py
  - experiments/thompson-f-p22-2026-09-17/tuples_model.py
---

Notation as in `thompson-f-caterpillar-tuples-cannot-certify-p22`. `C` is the caterpillar class or the vine class.
Both classes contain the leaf and are closed under taking subtrees. `S = S(n -> k)` with `d = n - k = 2`. Every
`s ∈ S` is a *symbolic forest*: `k` entries whose leaves are labelled `0, ..., n-1` in order, with two internal
nodes. Every leaf label sits at depth at most 2.

## Step 1. Reduction to head tuples

In the forest model, `s · y` adds the carets of `s` on roots `0..n-1` of `y`. The tail `(t_n, t_(n+1), ...)`
reappears unchanged at positions `k, k+1, ...`. Forests correspond bijectively to elements of `M` through the
normal form; this is checked in `tuples_model.py`.

Write `Y = ⊔_τ Y_τ` by tail `τ`, and let `A_τ ⊆ T^n` be the heads. Then `S Y_τ` consists of the forests with head
in `S A_τ` and tail `τ`. Different tails give disjoint image sets, so `|S Y| = Σ_τ |S A_τ|`. It therefore suffices
to prove `|S A| >= c |A|` for finite nonempty `A ⊆ C^n`.

## Step 2. Discharging

- Each `s` is injective on `T^n`. For `u ∈ T^k` there is at most one `b` with `s b = u`: `u` must contain the
  internal nodes of `s`, and then `b_j` is the subtree of `u` at the position of leaf `j`.
- Put `deg(u) = #{ s ∈ S : s^(-1) u exists and lies in C^n }`. For `u = s a` with `a ∈ C^n`, `s` itself is
  counted, so `deg(u) >= 1`.
- Every pair `(a, s)` with `a ∈ A ⊆ C^n` sends weight `1 / deg(s a)` to `s a`. The pairs landing on a fixed `u`
  have distinct `s`, each counted in `deg(u)`, so `u` receives at most 1. Hence

  `|S A| >= Σ_(a ∈ A) φ(a)`, where `φ(a) = Σ_(s ∈ S) 1 / deg(s a)`,

  and so `|S A| / |A| >= inf_(C^n) φ`.

## Step 3. φ depends only on root types

The **type** of a tree `t ∈ C` is
- 0 if `t` is a leaf,
- 1 if `t = (leaf, leaf)`,
- 2 if `t = (p, leaf)` with `p` not a leaf,
- 3 if `t = (leaf, q)` with `q` not a leaf.

Every non-leaf tree in `C` has a leaf child, so these four cases exhaust `C`.

Fix `a ∈ C^n`, `s`, `s'`, and `u = s a`. Whether `s'^(-1) u` exists and lies in `C^n` depends on two things:
- **(i)** whether the nodes of `u` at depth `<= 1` that `s'` needs are internal;
- **(ii)** whether the subtrees of `u` at the depth `<= 2` positions of the leaves of `s'` lie in `C`.

Every node of `u` at depth `<= 2` is of one of three kinds:
- (α) one of the two carets added by `s`;
- (β) the root of some `a_j`;
- (γ) a proper descendant of the root of `a_j`, at depth `<= 2` in `u`.

For (i):
- α nodes are internal.
- A β node is internal iff `type(a_j) ≠ 0`.
- A γ node at depth `<= 1` of `u` is a child of the root of an unmerged `a_j`, so its internality is read off
  `type(a_j)`.

For (ii):
- The subtree at a β or γ node is a subtree of `a_j`, so it lies in `C` by subtree closure.
- The subtree at an α node is `(p, q)`, `((p, q), r)` or `(p, (q, r))`, with `p, q, r` consecutive whole entries
  of `a`. Its membership in `C` is decided by the types of `p, q, r`:
  - **Caterpillars.** `(p, q) ∈ C` iff `p` or `q` is a leaf. `((p, q), r) ∈ C` iff `(p, q) ∈ C` and `r` is a
    leaf. `(p, (q, r)) ∈ C` iff `p` is a leaf and `(q, r) ∈ C`.
  - **Vines.** Let `Lv` and `Rv` be the left and right vines, each containing the leaf and the single caret, so
    `C = Lv ∪ Rv`. For a vine `p`, `p ∈ Lv` iff `type(p) ∈ {0, 1, 2}`, and `p ∈ Rv` iff `type(p) ∈ {0, 1, 3}`.
    - `(p, q) ∈ Lv` iff `p ∈ Lv` and `q` is a leaf.
    - `(p, q) ∈ Rv` iff `p` is a leaf and `q ∈ Rv`.
    - `((p, q), r) ∈ C` iff `(p, q) ∈ Lv` and `r` is a leaf.
    - `(p, (q, r)) ∈ C` iff `p` is a leaf and `(q, r) ∈ Rv`.

So `deg(s a)` is a function of `s` and of the type vector of `a`. Hence `φ(a)`
is a function of the type vector alone.

The representatives `leaf`, `(leaf, leaf)`, `((leaf, leaf), leaf)` and `(leaf, (leaf, leaf))` lie in both classes
and realise the four types. Hence `inf_(C^n) φ` is a minimum over the `4^n` representative tuples.

## Step 4. The finite computation

`types_check.py` evaluates `φ` in exact rationals on all `4^n` representative tuples. It computes `deg` by
explicit matching of all symbolic forests against `u` and class tests on the pieces, not by counting inside a
universe. Minima:

| set | `n -> k` | `min φ`, caterpillars | `min φ`, vines |
|---|---|---|---|
| `X_1` | 3 -> 2 | 1 | 1 |
| `X_2` | 4 -> 3 | 4/3 | 4/3 |
| `S_(2,4)` | 4 -> 2 | 5/3 | 5/3 |
| `S_(3,5)` | 5 -> 3 | **13/6** | **12/5** |
| `S_(4,6)` | 6 -> 4 | 49/18 | 1129/360 |

- For `S_(3,5)` on caterpillars the minimum is attained at 8 type vectors, for example `(2, 0, 2, 0, 2)`.
- For `S_(3,5)` on vines it is attained only at `(2, 0, 0, 0, 3)`.

As an independent check of Step 3, the script evaluates `φ` on every tuple of `C^n` with at most 8 carets
(23,392 caterpillar tuples and 5,072 vine tuples for `n = 5`). It asserts that `φ` equals the value of its type
vector.

During development the same check failed for the `d = 3` set `S(5 -> 2)`, as it should, so that case was removed from the script: there leaf positions reach depth 3 and the
four-valued types are too coarse. The theorem is claimed only for `d = 2`. Steps 1–4 give items 1–3 of the
claim.

**Run:** `cd experiments/thompson-f-p22-skeleton-2026-09-17 && python3 types_check.py 8`, about 10 seconds.
