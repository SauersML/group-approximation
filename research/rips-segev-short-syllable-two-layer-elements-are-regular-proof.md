---
rg: 2
id: rips-segev-short-syllable-two-layer-elements-are-regular-proof
kind: route
title: A zero divisor u(x)+w(x)y forces every support point to have a y-neighbour and a short x-neighbour; the alternating walk this gives is a short-syllable relation, which small cancellation forbids
target: rips-segev-short-syllable-two-layer-elements-are-regular
requires: [rips-segev-core-large-gap-two-layer-elements-are-regular, rips-segev-witness-divisors-need-saturated-supports, rips-segev-cores-have-no-infinite-cyclic-quotient, rips-segev-port-data-cannot-exclude-balanced-divisors]
---

**Conventions.**
- `G` is a group and `x, y in G`.  `k[t^{±1}]` is the Laurent polynomial ring, a PID.  For `f in k[t^{±1}]`,
  `f(x) in k[G]` is its image, and `supp f ⊆ Z` its exponent support.
- For `u, w in k[t^{±1}]` not both zero, the *joint span* is `max - min` of `supp u ∪ supp w`.
- The anti-involution `*` of `k[G]` is `g -> g^{-1}` extended linearly.  So `(alpha beta)^* = beta^* alpha^*`, and
  `f(x)^* = f^*(x)` with `f^*(t) = f(t^{-1})`.  Also `t -> t^{-1}` is a ring automorphism of `k[t^{±1}]`, so it
  preserves coprimality and joint span.
- Graph conventions are those of `rips-segev-core-large-gap-two-layer-elements-are-regular-proof`.
  - `Gamma` is a generalized Rips--Segev graph with reduced labelling satisfying `Gr'_*(1/8)`, and
    `K = F/<<R>>` with `F = <a> * <b>`.
  - The vertices are the line vertices `v_il`, `0 <= l <= C_i`, with no two identified.  The `a`-edges run
    `v_il -> v_{i,l+1}`.
  - `K` is torsion-free and `a != 1 != b` in `K`, so `a` and `b` have infinite order.
- A position `l` of line `i` is *distinguished* if `v_il` is an endpoint of some `b`-edge.  By the gluing
  description in `rips-segev-witness-supports-carry-no-zero-divisors-proof` ("Vertices of `Gamma`"), the
  distinguished positions of line `i` lie in `D_i = {0, C_i} ∪ I_i ∪ O_i`.
- `m_Gamma` is the least `|l - l'|` over distinct distinguished positions `l, l'` of one line.

**Steenbock's table.**  Line `i` has `(I_i1, I_i2, O_i1, O_i2, C_i) = (10^{5i-4}, 10^{5i-3}, 10^{5i-2}, 10^{5i-1}, 10^{5i})`.
So `D_i = {0} ∪ {10^{5i-4}, ..., 10^{5i}}`.
- Its least difference is `10^{5i-4} - 0`.
- Any other difference is `10^e - 10^{e'}` with `e > e' >= 5i-4`, which is at least `9 · 10^{5i-4}`.
- Hence `m_Gamma >= 10`.

---

## 1. Reduction to coprime, independent layers

**Lemma 1.**  Let `G` be torsion-free, with `x != 1 != y`.  Let `u, w in k[t^{±1}]` be not both zero, with
`g = gcd(u, w)`, `u = g u'` and `w = g w'`.  Put `beta = u(x) + w(x) y` and `beta' = u(x) + y w(x)`.
- (a) `beta = g(x) (u'(x) + w'(x) y)` and `beta' = (u'(x) + y w'(x)) g(x)`.
- (b) Nonzero elements of `k[<x>]` are non-zero-divisors in `k[G]`.
- (c) If `u'` or `w'` is zero, or `u'`, `w'` are linearly dependent over `k`, then `u' + w' y` and `u' + y w'` are
  non-zero-divisors.

So `beta` and `beta'` are non-zero-divisors unless `u'`, `w'` are coprime, both nonzero and linearly
independent.  In that remaining case they are non-zero-divisors as soon as `u' + w' y` and `u' + y w'` are.

*Proof.*
- (a) `u(x), w(x), g(x)` commute, so `g(x)u'(x) = u(x)`.  Then `y w(x) = y w'(x) g(x)` gives the second factorization.
- (b) `x` has infinite order, so `k[<x>] ≅ k[t^{±1}]` is a domain.  `k[G]` is a free left and a free right
  `k[<x>]`-module, on right and on left coset representatives.  So `f alpha = 0` with `f != 0` gives
  `f alpha_R = 0` on each right coset, and each `alpha_R = 0`.  The other side is the same.
- (c) If `w' = 0`, both elements are `u'(x) != 0`, handled by (b).  If `u' = 0`, they are `w'(x) y` and `y w'(x)`:
  a non-zero-divisor times a unit.  If both are nonzero and dependent, then `w' = lambda u'`.  Coprimality makes
  `u'` a unit, so `u' = mu t^j`.  Then `u' + w' y = mu x^j (1 + lambda y)` and `u' + y w' = (1 + lambda y) mu x^j`.
  Now `y` has infinite order, so `1 + lambda y` is a nonzero element of the domain `k[<y>]`, a non-zero-divisor by
  (b) applied to `y`.
- Products of non-zero-divisors are non-zero-divisors. ∎

---

## 2. The neighbour lemma

**Lemma 2 (cluster lemma).**  Let `u, w in k[t^{±1}]` be linearly independent with joint span `d`.  Let
`g_1, g_2 in k[t^{±1}]` satisfy `w g_1 = u g_2`, and put `P = supp g_1 ∪ supp g_2`.  Then every `n in P` has some
`n' in P` with `1 <= |n - n'| <= d`.

*Proof.*
- Multiplying `u` and `w` by a common power of `t` changes neither the hypothesis nor `d`.  So assume
  `supp u ∪ supp w ⊆ [0, d]`.  Independence forces `d >= 1`.
- Suppose `n in P` has `P ∩ [n - d, n + d] = {n}`.  Fix `m in [n, n + d]`.
  - The coefficient of `t^m` in `w g_1` is `sum_{j=0}^{d} w_j g_1(m - j)`.
  - Here `m - j in [n - d, n + d]`, and there `g_1` is supported only at `n`.  So this coefficient is
    `w_{m-n} g_1(n)`.
  - Likewise the coefficient of `t^m` in `u g_2` is `u_{m-n} g_2(n)`.
- As `m` runs over `[n, n + d]`, `m - n` runs over all of `[0, d]`.  So `g_1(n) w = g_2(n) u`.
- Since `n in P`, `(g_1(n), g_2(n)) != (0, 0)`.  This is a nontrivial linear relation between `u` and `w`, a
  contradiction. ∎

Write `(Y)` and `(X_d)` for the following properties of a subset `V ⊆ G`:
- `(Y)`: every `p in V` has `p y in V` or `p y^{-1} in V`.  This is symmetric in `y <-> y^{-1}`.
- `(X_d)`: every `p in V` has `p x^n in V` for some `1 <= |n| <= d`.

**Lemma 3 (neighbour lemma).**  Let `x in G` have infinite order.  Let `u, w in k[t^{±1}]` be linearly independent
with joint span `d`.
- (a) If `alpha (u(x) + w(x) y) = 0` with `alpha != 0`, then `V = supp(alpha u(x)) ∪ supp(alpha w(x))` is finite and
  nonempty, and satisfies `(Y)` and `(X_d)`.
- (b) Suppose also that `u, w` are coprime.  If `alpha (u(x) + y w(x)) = 0` with `alpha != 0`, then
  `V = supp alpha ∪ supp(alpha y)` is finite and nonempty, and satisfies `(Y)` and `(X_d)`.
- (c) Suppose also that `u, w` are coprime.  If `(u(x) + w(x) y) alpha = 0` or `(u(x) + y w(x)) alpha = 0` with
  `alpha != 0`, then some finite nonempty `V ⊆ G` satisfies `(Y)` and `(X_d)`.

*Proof.*  Decompose over left cosets `T = z<x>`: `alpha = sum_T alpha_T`.  Right multiplication by `f(x)` maps
`T` to itself, so the `T`-part of `alpha f(x)` is `alpha_T f(x)`.  Write `alpha_T = z f_T(x)`.

(a).
- `alpha u = - alpha w y`, so `A := supp(alpha u) = B y` with `B := supp(alpha w)`.  Hence:
  - each `p in A` has `p y^{-1} in B ⊆ V`;
  - each `p in B` has `p y in A ⊆ V`.
  This is `(Y)`.
- `alpha != 0` gives some `alpha_T != 0`.  Then `f_T u != 0` in the domain `k[t^{±1}]`, so `V` is nonempty.  It is
  finite since `alpha` has finite support.
- `V ∩ T = z x^P`, with `P = supp(f_T u) ∪ supp(f_T w)`.  Here `g_1 = f_T u` and `g_2 = f_T w` satisfy
  `w g_1 = u g_2`.  Lemma 2 gives `(X_d)` on `V ∩ T`, and `x` has infinite order, so exponents in `P` match
  elements of `T` one to one.

(b).
- `alpha u = - (alpha y) w`.  Taking `T`-parts, `alpha_T u = - (alpha y)_T w`.  Write `(alpha y)_T = z h_T(x)`.
  Then `f_T u = - h_T w` in `k[t^{±1}]`.
- By coprimality `w | f_T`: `f_T = w e_T` and `h_T = - u e_T`.
- `(Y)`: `p in supp alpha` gives `p y in supp(alpha y)`, and `p in supp(alpha y)` gives `p y^{-1} in supp alpha`.
- `V` is finite, and nonempty because `alpha != 0`.
- `V ∩ T = z x^P` with `P = supp(u e_T) ∪ supp(w e_T)`.  Here `g_1 = u e_T`, `g_2 = w e_T` satisfy
  `w g_1 = u g_2`, and Lemma 2 gives `(X_d)`.

(c).
- `(u + w y) alpha = 0` gives `alpha^* (u^* + y^{-1} w^*) = 0`.  This is case (b) with `y^{-1}` for `y` and `u^*, w^*`
  for `u, w`, which are still coprime and independent with joint span `d`.
- `(u + y w) alpha = 0` gives `alpha^* (u^* + w^* y^{-1}) = 0`, which is case (a) with `y^{-1}`.
- `alpha^* != 0`.  Property `(Y)` for `y^{-1}` is `(Y)` for `y`, and `(X_d)` does not involve `y`. ∎

**Lemma 4 (alternating walk).**  If a finite nonempty `V ⊆ G` satisfies `(Y)` and `(X_d)`, then
`x^{n_1} y^{e_1} x^{n_2} y^{e_2} ... x^{n_L} y^{e_L} = 1` in `G`, with `L >= 1`, `1 <= |n_k| <= d` and
`e_k in {±1}`.

*Proof.*
- For `p in V`, choose `n(p)` with `1 <= |n(p)| <= d` and `q = p x^{n(p)} in V`, by `(X_d)`.  Then choose
  `e(q) = ±1` with `q y^{e(q)} in V`, by `(Y)`.  Put `phi(p) = p x^{n(p)} y^{e(q)}`.
- `phi` maps the finite set `V` to itself.  So `phi^i(p_0) = phi^j(p_0)` for some `i < j`.
- With `p_k = phi^k(p_0)`, this gives `p_i = p_i x^{n_1} y^{e_1} ... x^{n_L} y^{e_L}` with `L = j - i`.  Cancel `p_i`. ∎

The word `W = x^{n_1} y^{e_1} ... x^{n_L} y^{e_L}` alternates nonzero powers.  In `<x> * <y>` (with `x`, `y` of
infinite order) it is a cyclically reduced normal form of free product length `2L`.

---

## 3. Short-syllable alternating relations do not hold in `K`

**Lemma 5.**  Let `L >= 1` and let `n_k, e_k` be nonzero integers.  If
`W = a^{n_1} b^{e_1} ... a^{n_L} b^{e_L} = 1` in `K`, then `|n_k| >= m_Gamma` for some `k`.

In particular, if `m_Gamma >= 2` then `b^{n_1} a^{e_1} ... b^{n_L} a^{e_L} != 1` in `K` for all nonzero `n_k` and
all `e_k in {±1}`.  Indeed a cyclic conjugate of this word has the form `W` with every `a`-exponent `±1`.

*Proof.*  `W` is a cyclically reduced normal form in `F` with `|W|_* = 2L`, hence nontrivial in `F`.  Suppose
`W = 1` in `K` and every `|n_k| < m_Gamma`.  Take a minimal van Kampen diagram `D` for `W` over `R`, and the
diagram `D̃` obtained by deleting originating edges.  Use the *standing reading* of
`rips-segev-core-large-gap-two-layer-elements-are-regular-proof`, Lemma 3:
- the boundary of `D` reads the cyclic normal form;
- each face `M` of `D̃` lifts with its boundary to a reduced, backtrack-free cycle `c_M` of `Gamma`;
- a boundary subpath `s` of `M` lifts to a subpath `c_s` whose letters form a freely reduced word equal to
  `omega(s)` in `F`.

So, by uniqueness of normal forms, `c_s` reads each complete syllable of `omega(s)` along a segment of
consecutive edges with one label and one orientation.

**Claim A'.**  Let `M` be a face of `D̃` with a connected exterior arc `s`.  Suppose that either `s` is the whole
boundary of `D` with `|omega(s)|_* >= 2`, or `s` is a proper subpath with `|omega(s)|_* >= 6`.  Then some
`|n_k| >= m_Gamma`.

*Proof of Claim A'.*
- As in Claim A of the large-gap proof, `omega(s)` contains at least four consecutive complete syllables of the
  cyclic word `W` in the proper case, and all syllables read cyclically in the whole-cycle case.
- The syllables alternate between `a`-powers and `b`-powers.  So `omega(s)` contains a complete block
  `b^{e} a^{n_k} b^{e'}`.
- The segment of `c_s` reading `a^{n_k}` is `|n_k|` consecutive `a`-edges of one orientation.  That is a monotone
  path along one line `i`, from `v_ip` to `v_{i,p+n_k}`.
- It is preceded by the segment reading `b^{e}`, whose last edge is a `b`-edge (traversed forward or backward)
  ending at `v_ip`.  It is followed by the segment reading `b^{e'}`, whose first edge is a `b`-edge starting at
  `v_{i,p+n_k}`.
- So `p` and `p + n_k` are distinguished positions of line `i`.  They are distinct because `n_k != 0`, so
  `|n_k| >= m_Gamma`.
- When `L = 1` in the whole-cycle case, the flanking syllables are the same syllable read at its two ends.  The
  argument uses only the edge adjacent to each end of the `a`-segment, so it is unchanged. ∎

*Case analysis.*  It is word for word the case analysis in Lemma 3 of the large-gap proof, which needs only
`|omega(∂M)|_* >= gamma >= 9` and the graphical small cancellation lemma.
- *No face.*  Then `W = 1` in `F`, which is false.
- *One face.*  `∂M = ∂D` is a whole-cycle exterior arc with `|omega|_* >= 9`.
- *Two faces.*  The exterior arc of `M_1` is connected, with `|omega|_* > (7/8) gamma > 7`.
- *More than two faces.*  Some face has a connected exterior arc with `|omega|_* > (1 - 3/8) · 9 > 5`.

In every case Claim A' applies and contradicts `|n_k| < m_Gamma` for all `k`. ∎

*Remark.*  Lemma 5 generalizes Lemma 3 of the large-gap proof from positive relations (`b`-exponents all `+1`)
to arbitrary nonzero `b`-exponents.  The price is that `Delta = {q - p : p in T_i, q in S_i}` is replaced by the set of all
differences of distinguished positions: when `b`-edges are traversed in both directions, the ends of an `a`-run
can both be sources or both be targets.  The same referee point applies as there: the lifting convention for
faces whose boundary meets `∂D`.

---

## 4. The theorems

**Theorem 1.**  If `m_Gamma >= 2`, every nonzero element of `k[<b>] + a k[<b>]` or of `k[<b>] + k[<b>] a` is a
non-zero-divisor in `k[K]`.

*Proof.*
- Write the element as `u(b) + a w(b)` or `u(b) + w(b) a`, with `u, w` not both zero.  Put `x = b` and `y = a`.
- `K` is torsion-free and `a, b != 1`.  By Lemma 1 we may assume `u, w` coprime, both nonzero and linearly
  independent, of some joint span `d`.
- If the element is a left or right zero divisor, Lemma 3 (a), (b) or (c) gives a finite nonempty `V ⊆ K`
  satisfying `(Y)` and `(X_d)` for `(x, y) = (b, a)`.
- Lemma 4 then gives `b^{n_1} a^{e_1} ... b^{n_L} a^{e_L} = 1` in `K`, with `L >= 1` and `n_k != 0`.  This
  contradicts the second statement of Lemma 5. ∎

**The witness support.**  `beta = c_0 + c_1 a + c_2 b + c_3 ab = (c_0 + c_2 b) + a (c_1 + c_3 b)` lies in
`k[<b>] + a k[<b>]`.  So Theorem 1 makes every nonzero `beta` supported on `{1, a, b, ab}` a non-zero-divisor,
for every field `k` and whatever `D` is.  Rank one (`D = 0`) is also Lemma 1 of
`rips-segev-witness-divisors-need-saturated-supports-proof`.  The mirror support `{1, a, b, ba}` is covered by
`k[<b>] + k[<b>] a`.

**Theorem 2.**  Let `u, w in k[t^{±1}]` be not both zero, with reduced span `d(u, w) < m_Gamma`.  Then `u(a) + w(a) b`
and `u(a) + b w(a)` are non-zero-divisors in `k[K]`.

*Proof.*
- Put `x = a` and `y = b`.  By Lemma 1 we may assume `u, w` coprime, both nonzero and independent, with joint span
  `d = d(u, w)`.
- A zero divisor gives, by Lemma 3, a finite nonempty `V` satisfying `(Y)` and `(X_d)`.
- Lemma 4 gives `a^{n_1} b^{e_1} ... a^{n_L} b^{e_L} = 1` with all `1 <= |n_k| <= d < m_Gamma`.
- This contradicts Lemma 5. ∎

For Steenbock's graphs (`m_Gamma >= 10`) this covers every reduced span `<= 9`.  Example:
`beta = (1 + a) + (1 + lambda a) b`.
- For `lambda != 1`, `u = 1 + t` and `w = 1 + lambda t` are coprime and independent with span 1.
- For `lambda = 1`, Lemma 1(c) applies.
- Here both offsets `delta_±` lie in `{-1, 0, 1}`, in the balanced box where
  `rips-segev-core-large-gap-two-layer-elements-are-regular` and its obstruction
  `rips-segev-port-data-cannot-exclude-balanced-divisors` stop.

**Transfer to `G(Gamma)`.**  The argument is the transfer paragraph of the large-gap proof.
- `K` embeds in `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2`.
- For `beta in k[K]` and `alpha = sum_j t_j alpha_j` over left cosets `t_j K`, `alpha beta = 0` forces every
  `alpha_j beta = 0`.
- Right cosets handle `beta alpha = 0`.

So Theorems 1 and 2 hold in `k[G(Gamma)]`. ∎

---

## 5. No left-orderable quotient (Steenbock's graphs)

**Proposition 6.**  For Steenbock's explicit graphs, every homomorphism `rho : K -> Q` to a left-orderable group
is trivial.

*Proof.*
- By Part 2 of `rips-segev-port-data-cannot-exclude-balanced-divisors-proof`, `K` satisfies two positive
  relations `b a^{n_1} ... b a^{n_L} = 1` and `b a^{m_1} ... b a^{m_M} = 1`, with `L, M >= 1`, all
  `n_k >= 99900` and all `m_k <= -10`.  These are cyclic conjugates of the labels of an `x_2`-cycle and an
  `x_1`-cycle.
- Fix a left order `<` on `Q`.  If `g, h > 1` then `gh > g · 1 = g > 1`, so products of positive elements are
  positive, and likewise for negative elements.  Put `A = rho(a)` and `B = rho(b)`.
- If `A = 1`, the first relation gives `B^L = 1`.  Left-orderable groups are torsion-free, so `B = 1`.
- If `B = 1`, the first relation gives `A^{sum n_k} = 1` with `sum n_k > 0`, so `A = 1`.
- Otherwise `A, B != 1`.
  - `A > 1, B > 1`: every factor `B`, `A^{n_k}` of the first relation is `> 1`, so the product is `> 1`.
  - `A < 1, B < 1`: every factor of the first relation is `< 1`.
  - `A > 1, B < 1`: the second relation has factors `B < 1` and `A^{m_k} < 1`.
  - `A < 1, B > 1`: the second relation has factors `B > 1` and `A^{m_k} > 1`.
  Each case contradicts the product being `1`.
- So `A = B = 1`, and `rho` is trivial since `a, b` generate `K`. ∎

A countable group acting nontrivially on `R` by orientation-preserving homeomorphisms has a nontrivial
left-orderable image in `Homeo_+(R)`.  So `K` has no such action.  This strengthens the bi-orderable and
locally indicable cases of `rips-segev-cores-have-no-infinite-cyclic-quotient`.  It kills the plan of reaching a
unique-product quotient of `K` through a left order, at the step "choose the signs of `rho(a)`, `rho(b)`".
Unique-product quotients that are not left-orderable are not excluded.

---

## 6. Calibration, and what the argument answers

**Calibration.**
- *`F_2`.*  Lemma 4's relation is a nonempty cyclically reduced word, never trivial.  So the lemmas reprove that
  these elements are regular in `k[F_2]`.
- *`Z^2 = <a> × <b>`.*  `a b a^{-1} b^{-1}` is an alternating relation with `|n_k| = 1`, so Lemma 5 fails there
  and the method is silent.  Nothing false is derived, and `k[Z^2]` is indeed a domain.
- *`Z/2 × Z/2`.*  `alpha = 1 + a + b + ab` and `beta = 1 + a + b - 3ab` give `alpha beta = 0`.  Here
  `u = 1 + t`, `w = 1 - 3t` are coprime and independent, but `a` has finite order.  In Lemma 3 finite order of
  `x` only matters for nonemptiness of `V` and for the injectivity `P -> T`, which holds once `ord(x) >= 2d + 2`.
  The walk reads `abab = 1`, which is an alternating relation that does hold.
- *Trefoil `<a, b | a b^3 a^{-1} b^{-3}>`.*  This is an alternating relation with long `b`-syllables.  So the
  abstract implication "no alternating relation, hence regular" has a real hypothesis; in `K` it is supplied by
  Lemma 5.
- *Finite groups, by computation.*  `experiments/rips-segev-short-syllable-2026-09-17/neighbour_check.py`
  computes full left kernels of right multiplication by `u(x) + w(x) y` over `GF(2), GF(3), GF(5)`.
  - Coverage: random 2-generator permutation groups of order 8 to 130, both roles `(x, y) = (a, b), (b, a)`, spans
    `d = 1, 2`, and `ord(x) >= 2d + 2`.  It checks `(Y)` and `(X_d)` on every basis vector and on random
    combinations, then closes the walk of Lemma 4 and checks that the word is trivial with the stated exponent
    bounds.
  - Result (`results.txt`, seeds 1 to 3): 124 configurations, 30393 kernel vectors, 0 lemma failures, 0 walk
    failures.
  - 1212 vectors have `alpha u = alpha w = 0`, so `V` is empty.  This is possible only because `x` has finite
    order, and those vectors are counted separately.

**Relation to the saturated-support node.**
- `rips-segev-witness-divisors-need-saturated-supports` reduced rank-two witness divisors to the non-existence
  of finite saturated sets, conditions (N) and (C).
- Theorem 1 answers the question behind that step directly: for `m_Gamma >= 2` no zero divisor is supported on
  `{1, a, b, ab}`.
- It does not decide whether finite `Sigma`-saturated sets exist in `K`.  The neighbour conditions `(Y)`, `(X_1)`
  are necessary conditions of a different kind: they use both coefficient equations at `p` and `p y`.  Unlike
  (N) and (C), they are refutable by a single small-cancellation diagram.

**What remains open.**
- Two-layer elements `u(a) + w(a) b` with reduced span `d >= m_Gamma` whose offsets lie in the large-gap box.
  For Steenbock's graphs these have `10 <= d` and `delta_± in [-N, N]`.  There, Lemma 4 yields relations with
  `|n_k| <= d`, and `Gamma` does carry such relations (the `x_1`-cycles have `|n_k| = 10^{5l-4}`).  So the next
  input must again be coefficient data along the walk, not the walk alone.
- Elements meeting three or more `b`-layers, such as `u(a) + w(a) b + z(a) b^2` with short `a`-span.  Lemma 3 has
  no proved analogue there.  The wanted statement is that every point of a suitable finite `V` has a neighbour
  among `p b^{±1}, p b^{±2}`, and a neighbour `p a^n` with `1 <= |n| <= d`.  Lemma 4 would then close a walk with
  short `a`-syllables, and Lemma 5 already allows arbitrary nonzero `b`-exponents.  So the missing input is a
  three-layer neighbour lemma.  It is a local statement about Laurent polynomials, testable in finite groups with
  the same script.
