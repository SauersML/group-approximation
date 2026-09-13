---
rg: 2
id: half-finite-shift-envelope-wp-computes-generators-proof
kind: route
title: Test conjugates of explicit transposition words against candidate transpositions
target: half-finite-shift-envelope-wp-computes-generators
requires: []
---

**Step 1. The slide is a translation of a line.** Put `L_p = 2p+1` for `p >= 0`
and `L_p = -2p` for `p < 0`. This is a bijection `Z -> N`, and
`pos(L_p) = p` satisfies `|pos(x)| <= x`. The slide sends odd `x` to `x+2`,
even `x != 2` to `x-2`, and `2` to `1`. Checking the three cases gives
`sl(L_p) = L_(p+1)` for every `p`:
- `p >= 0`: `2p+1 -> 2p+3`;
- `p = -1`: `2 -> 1`;
- `p <= -2`: `-2p -> -2p-2`.

Also `(1 2) = (L_(-1) L_0)`.

**Step 2. Short transposition words.** For each `p`,

```text
tau_p := sl^p (1 2) sl^-p = ( L_(p-1)  L_p ),     word length 2|p| + 1,    (HFP1)
```

since conjugating a permutation relabels its support. For distinct `a, b` with
`u = pos(a) < v = pos(b)`, the standard identity

```text
( L_u L_v ) = tau_(u+1) tau_(u+2) ... tau_(v-1) tau_v tau_(v-1) ... tau_(u+1)   (HFP2)
```

writes `(a b)` as a product of `2(v-u) - 1` adjacent transpositions. Put
`m = max(a,b)`. Then `|u|, |v| <= m` and `v - u <= 2m`, so each factor has
length at most `2m+1` and there are at most `4m` factors. This gives an explicit
word `w(a,b)` over `X` of length at most `12 m^2`, computable in time `O(m^2)`.

**Step 3. The test.** For every permutation `g`, `g (a b) g^-1 = (g(a) g(b))`.
So for distinct `n, m` and distinct `c, d`,

```text
W(i;n,m;c,d) := gamma_i w(n,m) gamma_i^-1 w(c,d)^-1   is trivial in G
       iff   { gamma_i(n), gamma_i(m) } = { c, d }.                            (HFP3)
```

**Step 4. The algorithm.** Given `i` and `n`:
- Let `m_1 < m_2` be the two smallest elements of `{1,2,3} \ {n}`.
- For `B = 1, 2, 4, 8, ...`, test `W(i; n, m_j; c, d)` for `j = 1, 2` and all
  `1 <= c < d <= B`, using the word-problem algorithm. Stop at the first `B` for
  which both `j = 1` and `j = 2` have a passing pair `P_j`.
- Output the unique element of `P_1 ∩ P_2`.

**Correctness.** By (HFP3), `P_j = {gamma_i(n), gamma_i(m_j)}`. The points
`gamma_i(m_1)` and `gamma_i(m_2)` are distinct, and both differ from
`gamma_i(n)`, so `P_1 ∩ P_2 = {gamma_i(n)}`. The loop stops once
`B >= M := max(gamma_i(n), gamma_i(m_1), gamma_i(m_2))`, so the last `B` is
below `2M`. Also `M <= D(max(n,3)) <= D(n+3)`.

**Cost.**
- *Queries.* At most `sum over B <= 2M of 2B^2 <= 12 M^2`.
- *Word length.* Each query word has length at most
  `2 + 12 max(n,3)^2 + 12 (2M)^2 <= C_0 * D(n+3)^2`. Here `max(n,3) <= D(n+3)` is
  used, which holds after replacing `D` by `max(D, id+3)`; that changes no
  bound below.
- *Total.* Building words and bookkeeping cost `O(D(n+3)^2)` per query. The
  total is at most `C * D(n+3)^2 * ( T(C * D(n+3)^2) + D(n+3)^2 )`, which is
  (HFW2).

**Step 5. The consequence.** Suppose a word-problem algorithm over some finite
generating set `Y` runs in time `C_1 * T(C_1 l) + C_1 l + C_1`. Rewriting
`X`-words as `Y`-words multiplies length by a constant, so the `X`-word problem
runs in time `C_2 * T(C_2 l) + C_2 l + C_2`. Take the linear bound
`D(x) = K x + K` and replace `T` by `T'(l) = C_2 T(C_2 l) + C_2 l + C_2`. Then
(HFW2) evaluates `gamma_i(n)` in time at most

```text
C_3 * (n+3)^2 * ( T( C_3 (n+3)^2 ) + (n+3)^2 )  <=  C_4 * R( C_4 n ) + C_4 n + C_4,
```

with `R(n) = (n+3)^2 T((n+3)^2)`, using monotonicity of `T`. So evaluation lies
in `F(R)`, which is the contrapositive of the stated consequence. `∎`
