---
rg: 2
id: f2-set-spectral-laws-quotient-bounds-proof
kind: route
title: Express nu(B^perp) through the coset counts of S modulo B, then apply the coset-wise edge-isoperimetric inequality (proved by induction) and Jensen
target: f2-set-spectral-laws-obey-quotient-collision-and-harper-bounds
requires: []
---

Notation as in the target. For a subspace `B` of `F_2^k` of dimension `r`, let
the cosets of `B` be `C_1, ..., C_(N/2^r)` and `t_C = |S n C|`, so `sum_C t_C = s`.

## Step 1: collision identity

Since `(B^perp)^perp = B` and `|B^perp| = N/2^r`,

```text
sum_(chi in B^perp) f^(chi)^2 = N^(-2) sum_(x, x' in S) sum_(chi in B^perp) (-1)^(chi.(x+x'))
                              = N^(-2) (N / 2^r) #{(x, x') in S^2 : x + x' in B}
                              = N^(-1) 2^(-r) sum_C t_C^2 .
```

So `nu(B^perp) = sum_C t_C^2 / (s 2^r)`.   (1)

## Step 2: (M)

Given a character subspace `W` of dimension `j`, apply (1) with `B = W^perp`,
`r = k - j`. Each `t_C <= min(s, 2^r)`, so `sum_C t_C^2 <= s min(s, 2^r)`, and
`nu(W) <= min(s, 2^r)/2^r = min(1, s 2^j / N) = min(1, |W| s / N)`.

## Step 3: Harper's inequality on `Q_r`, proved

**Lemma.** For `A` a subset of `F_2^r`, let `e(A)` be the number of unordered
pairs `{z, z + e_i}` inside `A`. Then `e(A) <= (1/2) |A| log2 |A|`.

*Proof.* Induct on `r`. For `r = 0`, `|A| <= 1` and `e(A) = 0`. For `r >= 1`
split `A` by the last coordinate into `A_0, A_1` (copies in `F_2^(r-1)`) with
`x = |A_0| >= y = |A_1|` (swap names if needed). Edges inside `A` are edges
inside `A_0`, inside `A_1`, or matched pairs across, at most `y` of them. So
`e(A) <= (x log2 x + y log2 y)/2 + y` by induction. With `t = y/(x+y)` in
`[0, 1/2]`,
`(x+y) log2(x+y) - x log2 x - y log2 y = (x+y) h(t)`, where `h` is the binary
entropy. `h` is concave with `h(0) = 0` and `h(1/2) = 1`, so `h(t) >= 2t` on
`[0, 1/2]`, giving `x log2 x + y log2 y + 2y <= (x+y) log2(x+y)`. Hence
`e(A) <= (1/2) |A| log2 |A|`.  QED

Consequently the directed boundary `#{(z, i) : z in A, z + e_i not in A} = r|A| - 2 e(A) >= |A| (r - log2 |A|)`.   (2)

## Step 4: (H)

Let `b_1, ..., b_r` be independent with span `B`. Fix a coset `C = x_0 + B` and
identify it with `F_2^r` by `x_0 + sum z_i b_i <-> z`. Then `x + b_i` corresponds
to `z + e_i`. So the number of `(x, i)` with `x in S n C`, `x + b_i not in S`
is the directed boundary of the image of `S n C`, and by (2) it is at least
`t_C (r - log2 t_C)` when `t_C >= 1`. Summing over cosets and dividing by `s`,

```text
sum_i d_S(b_i) >= sum_C (t_C/s) (r - log2 t_C)
              >= r - log2( sum_C (t_C/s) t_C )          (Jensen: log2 concave, weights t_C/s)
              =  r - log2( 2^r nu(B^perp) )             (by (1))
              =  log2( 1 / nu(B^perp) ).
```

Finally `d_S(b) = 1 - sum_chi nu(chi) (-1)^(chi.b) = 2 nu{chi : chi.b = 1}`, since
`|S n (S + b)| = N sum_chi f^(chi)^2 (-1)^(chi.b)`. This gives (H).  QED

*Replay.* `python3 experiments/f2-cayley-dominance-2026-09-17/spectral_relaxation.py check 6 3 20 2`
tests (M) on every dual subspace of dimension `< c` and (H) at the minimum-weight basis of every
subspace `B` (the minimum over bases of `sum_i nu{chi.b_i = 1}` is found greedily, since it is a
min-weight basis of a linear matroid).
