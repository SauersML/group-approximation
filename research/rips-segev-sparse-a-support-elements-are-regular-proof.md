---
rg: 2
id: rips-segev-sparse-a-support-elements-are-regular-proof
kind: route
title: Every b-layer of a zero-divisor equation must cancel against another, and an isolated a-point would make the layers proportional; the alternating walk then reads a relation whose a-syllables lie in S - S, which small cancellation forbids
target: rips-segev-sparse-a-support-elements-are-regular
requires: [rips-segev-short-syllable-two-layer-elements-are-regular, rips-segev-core-large-gap-two-layer-elements-are-regular]
---

**Conventions.**  They are those of `rips-segev-short-syllable-two-layer-elements-are-regular-proof` (cited as
[SS]).
- `k[t^{±1}]` is the Laurent polynomial ring.  For `f` in it, `supp f ⊆ Z` is its exponent support, and `f(x)` is
  its image in `k[G]`.
- `*` is the anti-involution `g -> g^{-1}` of `k[G]`.  So `(alpha beta)^* = beta^* alpha^*`.
- For a finite `S ⊂ Z` put `N_S = (S - S) \ {0}`.
- `Dist(Gamma)` is the set of `l' - l`, over distinct distinguished positions `l, l'` of one line.  A position `l`
  of line `i` is distinguished if `v_il` is an endpoint of a `b`-edge.  `Dist(Gamma)` is finite, symmetric and
  does not contain 0.

---

## 1. Rank one factors

**Lemma 1.**  Let `G` be torsion-free with `x, y != 1`.  Let `beta = sum_{i in S, j in J} c_ij x^i y^j != 0`, and
suppose the matrix `C = (c_ij)` has rank 1.  Then `beta` is a non-zero-divisor in `k[G]`.

*Proof.*  Rank 1 gives `c_ij = r_i s_j` with `r != 0`, `s != 0`.  So `beta = h(x) v(y)` with
`h = sum r_i t^i != 0` and `v = sum s_j t^j != 0`.  By [SS] Lemma 1(b), nonzero elements of `k[<x>]` and of
`k[<y>]` are non-zero-divisors.  A product of non-zero-divisors is one. ∎

---

## 2. The multi-layer neighbour lemma

**Lemma 2 (cluster lemma).**  Let `u_j in k[t^{±1}]` (`j in J`) have supports in a finite `S ⊂ Z`, and let them
span a subspace of dimension `>= 2`.  Let `f in k[t^{±1}]` be nonzero, `g_j = f u_j` and
`P = union_j supp g_j`.  Then every `n in P` has some `n' in P` with `n' - n in N_S`.

*Proof.*
- Suppose `n in P` and `P ∩ (n + (S - S)) = {n}`.  Fix `i, j in J` and `s in S`, and put `m = n + s`.
- The coefficient of `t^m` in `g_i u_j` is `sum_{l in S} u_j(l) g_i(m - l)`.  Here `m - l in n + (S - S)`, where
  `g_i` is supported only at `n`.  So this coefficient is `u_j(s) g_i(n)`.
- Likewise the coefficient of `t^m` in `g_j u_i` is `u_i(s) g_j(n)`.
- Now `g_i u_j = f u_i u_j = g_j u_i`.  As `s` runs over `S`, this gives `g_i(n) u_j = g_j(n) u_i`.
- Since `n in P`, some `g_i(n) != 0`.  Then every `u_j = (g_j(n) / g_i(n)) u_i`, so the span has dimension
  `<= 1`.  This is a contradiction. ∎

For `S = [0, d]` this is [SS] Lemma 2, extended from two polynomials to any number.

Write, for `V ⊆ G`:
- `(Y_J)`: every `p in V` has `p y^e in V` for some `e in N_J`;
- `(X_S)`: every `p in V` has `p x^n in V` for some `n in N_S`.

**Lemma 3 (neighbour lemma).**  Let `x in G` have infinite order and `y in G`.  Let
`beta = sum_{j in J} u_j(x) y^j`, where the `u_j` have supports in `S` and span a space of dimension `>= 2`.  If
`alpha beta = 0` with `alpha != 0`, then `V = union_j supp(alpha u_j(x))` is finite, nonempty, and satisfies
`(Y_J)` and `(X_S)`.

*Proof.*  Put `A_j = alpha u_j(x)`, so that `sum_j A_j y^j = 0`.
- `(Y_J)`.  Let `p in supp A_i`.  Then `p y^i` has nonzero coefficient in `A_i y^i`.  The coefficient of `p y^i` in
  `sum_j A_j y^j` is 0.  So some `j != i` has `p y^i in supp(A_j y^j)`, that is, `p y^{i-j} in supp A_j ⊆ V`.
  Here `i - j in N_J`.
- Finiteness is clear.  Decompose `alpha` over left cosets `T = z<x>`, and write `alpha_T = z f_T(x)`.  Right
  multiplication by `u_j(x)` preserves `T`, so `(A_j)_T = z (f_T u_j)(x)`.
- Nonempty.  Some `f_T != 0`, and some `u_j != 0`.  In the domain `k[t^{±1}]`, `f_T u_j != 0`.
- `(X_S)`.  `V ∩ T = z x^P` with `P = union_j supp(f_T u_j)`.  Since `x` has infinite order, `n -> z x^n` is
  injective.  Lemma 2 with `f = f_T` gives `(X_S)` on `V ∩ T`. ∎

**Lemma 4 (walk).**  If a finite nonempty `V ⊆ G` satisfies `(Y_J)` and `(X_S)`, then
`x^{n_1} y^{e_1} ... x^{n_L} y^{e_L} = 1` in `G` with `L >= 1`, all `n_k in N_S` and all `e_k in N_J`.

*Proof.*  This is [SS] Lemma 4 word for word, with `(Y)` and `(X_d)` replaced by `(Y_J)` and `(X_S)`.
- For `p in V` choose `n(p) in N_S` with `q = p x^{n(p)} in V`.  Then choose `e(q) in N_J` with `q y^{e(q)} in V`.
  Put `phi(p) = q y^{e(q)}`.
- `phi` maps the finite set `V` to itself, so some orbit repeats.  The repeating segment reads the relation. ∎

---

## 3. The small-cancellation input

**Lemma 5 ([SS] Lemma 5, read exactly).**  Let `L >= 1` and let `n_k, e_k` be nonzero integers.  If
`a^{n_1} b^{e_1} ... a^{n_L} b^{e_L} = 1` in `K`, then some `n_k in Dist(Gamma)`.

*Proof.*  The proof of [SS] Lemma 5 assumes the relation and derives a contradiction from Claim A' in every case
of the van Kampen case analysis.  Claim A' finds a block `b^e a^{n_k} b^{e'}` of the relation that lifts to a
monotone `a`-path on one line `i`, from `v_ip` to `v_{i,p+n_k}`.  Both ends carry `b`-edges, so `p` and
`p + n_k` are distinct distinguished positions of line `i`.  That is exactly `n_k in Dist(Gamma)`.  [SS] then
concludes `|n_k| >= m_Gamma`, the weaker form. ∎

---

## 4. The theorem

**Theorem.**  Let `S, J ⊂ Z` be finite and `beta = sum_{i in S, j in J} c_ij a^i b^j != 0` in `k[K]`.  If
`N_S ∩ Dist(Gamma)` is empty, then `beta` is a non-zero-divisor in `k[K]`.

*Proof.*
- `K` is torsion-free and `a, b` have infinite order ([SS], conventions).  If `rank C <= 1`, Lemma 1 applies,
  since `beta != 0` forces `rank C = 1`.  So assume `rank C >= 2`.
- **Left annihilators.**  Write `beta = sum_j u_j(a) b^j` with `u_j = sum_i c_ij t^i`.
  - The `u_j` are the columns of `C`, so they span a space of dimension `rank C >= 2`, with supports in `S`.
  - Suppose `alpha beta = 0` with `alpha != 0`.  Lemma 3 with `(x, y) = (a, b)` gives `V`, and Lemma 4 gives
    `a^{n_1} b^{e_1} ... a^{n_L} b^{e_L} = 1` with `n_k in N_S` and `e_k in N_J`, all nonzero.
  - Lemma 5 gives some `n_k in Dist(Gamma) ∩ N_S`, which is empty.  Contradiction.
- **Right annihilators.**  Suppose `beta alpha = 0` with `alpha != 0`.  Then `alpha^* beta^* = 0` and
  `alpha^* != 0`, where `beta^* = sum_{i, j} c_ij b^{-j} a^{-i} = sum_{i in S} v_i(b) a^{-i}` with
  `v_i = sum_j c_ij t^{-j}`.
  - The `v_i` are the rows of `C`, up to `t -> t^{-1}`, an automorphism of `k[t^{±1}]`.  So they span a space of
    dimension `rank C >= 2`, with supports in `-J`.
  - Apply Lemma 3 with `(x, y) = (b, a)`, layer set `-S` and exponent set `-J`.  Then Lemma 4 gives
    `b^{m_1} a^{f_1} ... b^{m_L} a^{f_L} = 1` with `m_k in N_{-J}` and `f_k in N_{-S} = N_S`, all nonzero.
  - Conjugating by `b^{m_1}` gives `a^{f_1} b^{m_2} a^{f_2} ... b^{m_L} a^{f_L} b^{m_1} = 1`, of the form in
    Lemma 5.  So some `f_k in Dist(Gamma) ∩ N_S`, a contradiction. ∎

**Corollaries.**
1. *Mirror form.*  `sum c_ij b^j a^i` is the `*` of `sum c_ij a^{-i} b^{-j}`, whose exponent set `-S` has
   `N_{-S} = N_S`.  `*` preserves being a non-zero-divisor.
2. *Left `a`-factors.*  If `beta = g(a) beta'` with `g != 0` and `beta'` satisfies the theorem, then `beta` is a
   product of non-zero-divisors.
3. *Translates.*  `x beta y` with `x, y in K` is a non-zero-divisor iff `beta` is.
4. *Short span.*  If `S ⊆ [s_0, s_0 + d]` with `d < m_Gamma`, then `N_S ⊆ [-d, d]` misses `Dist(Gamma)`.  So
   every `sum_j u_j(a) b^j` of joint `a`-span `< m_Gamma` is regular, with any number of layers and any
   coefficients.  For three layers this is the statement asked for at the end of [SS].
5. *Steenbock's table.*  The distinguished positions of line `i` lie in `{0} ∪ {10^{5i-4}, ..., 10^{5i}}` ([SS],
   "Steenbock's table").  So every element of `Dist(Gamma)` is `± 10^e` with `e >= 1` or `± (10^e - 10^{e'})` with
   `e > e' >= 1`, a nonzero multiple of 10.  Hence the theorem applies whenever the elements of `S` are pairwise
   incongruent mod 10.  More generally it applies whenever `N_S` contains no number of the form
   `10^e` or `10^e - 10^{e'}` with `1 <= e' < e`.

**Transfer to `G(Gamma)`.**  It is the transfer paragraph of [SS] §4 and of
`rips-segev-core-large-gap-two-layer-elements-are-regular-proof`.
- `k[G(Gamma)]` is a free left and right `k[K]`-module.
- If `alpha beta = 0` with `beta in k[K]`, then `alpha = sum_l t_l alpha_l` over left cosets `t_l K`.  The terms
  `t_l alpha_l beta` lie in distinct cosets, so every `alpha_l beta = 0`, and every `alpha_l = 0`.
- Right cosets handle `beta alpha = 0`. ∎

---

## 5. Calibration and limits

**Calibration.**
- *`F_2`* (`Gamma` without cycles).  `Dist` may be nonempty, but no alternating word is trivial in `F_2`.  So
  Lemmas 3 and 4 alone reprove that these elements are regular in `k[F_2]`.
- *`Z^2`.*  `a b a^{-1} b^{-1} = 1` has `a`-exponents `±1`.  The method needs `1 ∉ N_S`, and it is correctly
  silent for `S ∋ 0, 1`.  For `S = {0, 2}` in `Z^2`, the relation `a^2 b a^{-2} b^{-1}` exists, so the method is
  silent there too.  The analogue of Lemma 5 fails in `Z^2` for every `S`.
- *`Z/2 × Z/2`.*  `(1 + a + b + ab)(1 + a + b - 3ab) = 0`, with `rank C = 2` and `S = J = {0, 1}`.  The walk reads
  `abab = 1`, a relation with `a`-exponent `1 in N_S`.  In a finite group Lemma 3 needs `ord(x) > 2 span(S)` for
  the windows and `ord(y) > span(J)` for `y^e != 1`.
- *Finite groups.*  `experiments/rips-segev-multilayer-2026-09-17/neighbour_multilayer.py` computes full left
  kernels of right multiplication by `beta` over `GF(2), GF(3), GF(5)`.
  - Coverage: random 2-generator permutation groups of order 8 to 130, both roles `(x, y) = (a, b), (b, a)`,
    layer sets `{0,1}, {0,2}, {0,3}, {0,1,2}, {0,1,3}, {-1,0,2}, {0,1,2,3}`, and exponent sets
    `{0,1}, {0,1,2}, {0,2}, {0,3}, {0,1,4}, {0,2,3}`.
  - It checks `(Y_J)` and `(X_S)` on every kernel basis vector and on random kernel combinations.  It closes the
    walk of Lemma 4 and checks that the word is trivial with `n_k in N_S`, `e_k in N_J`.
  - Result (`results.txt`, seeds 1 to 3): 180 configurations (40 with sparse `S`), 3131 elements of rank `>= 2`,
    34765 kernel vectors, 0 lemma failures and 0 walk failures.  Kernel vectors with empty `V`
    occur only because `x` has finite order.
  - Control: for rank-one coefficient matrices, `(X_S)` fails on 16526 of 26600 kernel vectors.  So the rank hypothesis
    in Lemma 3 cannot be dropped.

---

## 6. The chain criterion: a finite test on `Gamma` for the remaining elements

Lemma 5 reads one flanked block off an exterior arc.  The same arc carries many consecutive blocks, and this
turns the uncovered case into a finite search in `Gamma`.

Let `gamma` be the least free product length of a cycle label of `Gamma` (so `gamma >= 9`), and put
`q(gamma) = floor((floor(5 gamma / 8) - 3) / 2)`.  So `q(9) = 1`, and `q(gamma) >= 3` once `gamma >= 16`.

**Definition.**  An `(N_S, N_J)`-chain of length `q` is a backtrack-free path in `Gamma` whose label has normal
form `b^{e_0} a^{n_1} b^{e_1} ... a^{n_q} b^{e_q}` with every `n_k in N_S` and every `e_k in N_J`.
- Each `a^{n_k}` is then a monotone segment of one line whose two ends carry `b`-edges.  So `n_k in Dist(Gamma)`,
  and a chain of length 1 exists iff `N_S ∩ Dist(Gamma) != ∅` and suitable `b`-runs exist.

**Lemma 6 (chain lemma).**  Let `W = a^{n_1} b^{e_1} ... a^{n_L} b^{e_L}` with all exponents nonzero, `L >= 1`,
and `W = 1` in `K`.  Then `Gamma` contains a backtrack-free path reading
`b^{e_{k-1}} a^{n_k} b^{e_k} ... a^{n_{k+q-1}} b^{e_{k+q-1}}` for some `k`, with `q = q(gamma)` and indices mod `L`.

*Proof.*  Run the case analysis of [SS] Lemma 5, keeping the length of the exterior arc `s` of the chosen face.
- *One face.*  `s = ∂D`, so `2L = |W|_* >= gamma`.  Every syllable is complete, read cyclically.  Since
  `L >= gamma/2 >= q`, the cycle `c_M` read from any `b`-syllable carries the required `q` blocks.
- *Two faces.*  `|omega(s)|_* > (7/8) gamma`.  *More faces.*  `|omega(s)|_* > (5/8) gamma`.  In both cases
  `|omega(s)|_* >= floor(5 gamma / 8) + 1`.
- If `s` is proper, `omega(s) = x_0 sigma_1 ... sigma_r x_{r+1}` with `r >= |omega(s)|_* - 2` complete
  consecutive syllables of `W`.  The `a`-syllables among `sigma_2, ..., sigma_{r-1}` are flanked by complete
  `b`-syllables inside `sigma_1 ... sigma_r`.  There are at least `floor((r - 2)/2) >= q` of them, and they are
  consecutive.
- If `s = ∂D`, the one-face argument applies.
- *Lift.*  `c_s` is backtrack-free and reads each complete syllable along a run of edges of one label and one
  orientation, as in [SS] Claim A'. ∎

**Theorem 2 (chain criterion).**  Let `beta = sum_{i in S, j in J} c_ij a^i b^j != 0`.  If `Gamma` has no
`(N_S, N_J)`-chain of length `q(gamma)`, then `beta` is a non-zero-divisor in `k[K]` and in `k[G(Gamma)]`.

*Proof.*  As in §4.  The left case gives a relation with `a`-exponents in `N_S` and `b`-exponents in `N_J`.  The
right case gives one with `a`-exponents in `N_S` and `b`-exponents in `N_{-J} = N_J`.  Lemma 6 then produces a
chain of length `q(gamma)`. ∎

Theorem 1 is the case where no chain of length 1 exists.  For a given explicit `Gamma` and `S, J`, Theorem 2 is a
finite graph search.  Every hop `a^{n_k}` must join distinguished positions at distance in
`N_S ∩ Dist(Gamma)`.
- *Example.*  Take Steenbock's table, `J = {0, 1}` and `S ⊆ [0, 89]`: two-layer elements `u(a) + w(a) b` of
  joint `a`-span `<= 89`, such as `1 + a^{10} + b` or `(1 + a)^{10} + b`.
  - The elements of `Dist(Gamma)` of absolute value `<= 89` are `±10`, from positions 0 and 10 of line 1.  The
    next ones are `±90 = ±(100 - 10)`, and lines `i >= 2` only give values `>= 10^6`.
  - So every hop is the segment between `v_{1,0}` and `v_{1,10}`, and every `b`-run is a single `b`-edge.
  - A chain of length 2 therefore needs a `b`-edge joining two of `v_{1,0}, v_{1,10}`.  A `b`-edge has its source
    in `{0, C_j} ∪ O_j` and its target in `I_k ∪ {0, C_k}`, and it is not a loop (it would give `b = 1`).  The
    only candidate is an edge `v_{1,0} -> v_{1,10}`.
  - `q(gamma) >= 2` as soon as `gamma >= 12`.
- So if `gamma >= 12` and `Gamma` has no `b`-edge from `v_{1,0}` to `v_{1,10}`, then every `u(a) + w(a) b` of
  joint `a`-span `<= 89` is regular.
- Both inputs depend on the explicit gluing of Steenbock's graph, which is not recorded on main.  So the example
  is a reduction to two checkable facts about `Gamma`, not a proof.

**What is not covered.**
- Elements for which `Gamma` has `(N_S, N_J)`-chains of length `q(gamma)`.  For contiguous `S` of `a`-span
  above `max_i C_i` every relator label is such a chain, so Theorem 2 is silent.  There the coefficients along
  the walk must enter: Lemma 2 uses only the window around one point.
