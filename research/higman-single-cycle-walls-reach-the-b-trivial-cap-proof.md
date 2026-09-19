---
rg: 2
id: higman-single-cycle-walls-reach-the-b-trivial-cap-proof
kind: route
title: Proof by the order chain c^(n_2 - 1) = 1, d^(n_3^ord(c) - 1) = 1, a^(n_4^ord(d) - 1) = 1 for the upper bound, an explicit log-coordinate isometry for c on the valuation layers for the lower bound, blocks of the regular cyclic action for b, and an affine-mod-4 argument for rigidity
target: higman-single-cycle-walls-reach-the-b-trivial-cap
requires:
  - higman-h4-3-has-no-odometer-models-beyond-level-five
artifacts:
  - experiments/higman-single-cycle-cap-2026-09-19/captower.py
  - experiments/higman-single-cycle-cap-2026-09-19/captower-output.txt
---

The notation is that of the target. All four items are proved here in full. The only input
from `higman-h4-3-has-no-odometer-models-beyond-level-five` is its Lemma 1: every
level-transitive element of `W_M` is conjugate in `W_M` to the odometer `x -> x + 1`.
Permutations are functions, and `f∘g` means first `g`, then `f`. The model relations are
`a∘b∘a^-1 = b^(n_1)`, `b∘c∘b^-1 = c^(n_2)`, `c∘d∘c^-1 = d^(n_3)` and `d∘a∘d^-1 = a^(n_4)`.

**Two facts about 2-adic units.** (F1) For odd `u` and `e >= 1`, `v2(u^e - 1) = v2(u - 1)` if `e` is
odd, and `v2(u^e - 1) = v2(u^2 - 1) + v2(e) - 1` if `e` is even. In particular
`v2(3^e - 1) = 1` for odd `e`, and `v2(3^e - 1) = v2(e) + 2` for even `e`. So the multiplicative
order of `3^e` mod `2^N` is `2^max(0, N - v2(3^e - 1))` when `3^e ≡ 1 mod 4`. When
`3^e ≡ 3 mod 4` it is `2^(N-2)` for `N >= 3`, `2` for `N = 2` and `1` for `N <= 1`. (F2) For
`n >= 3` every unit mod `2^n` is uniquely `s 3^i` with `s = ±1` and `i mod L = 2^(n-2)`. For
`3 <= t <= n` two units `s 3^i` and `s' 3^(i')` are congruent mod `2^t` if and only if `s = s'`
and `i ≡ i' mod 2^(t-2)`. Mod 4, `s 3^i ≡ s (-1)^i`, and mod 2 all units agree. Both facts are
standard; (F2) follows from `<3>` mod `2^t` having order `2^(t-2)` and not containing `-1`
(`t >= 3`).

**Item 1, upper bound.** Let `a = x + 1`, `b = 1` be a single-cycle model of level `k`. The
relation `b∘c∘b^-1 = c^(n_2)` becomes `c = c^(n_2)`. Since `c` has 2-power order, `ord(c)` divides
`2^(v2(n_2 - 1)) = 2^gamma(m_b)`. From `c∘d∘c^-1 = d^(n_3)` we get
`c^r∘d∘c^-r = d^(n_3^r)`, so `r = ord(c)` gives `d = d^(n_3^r)`. Then `ord(d)` divides the 2-part of
`n_3^r - 1 = 3^(m_c r) - 1`, and by (F1) that 2-part is at most
`2^(gamma(m_b) + v2(m_c) + 2)`; the exponent `m_c r` is even or else `r = 1`, which only lowers it.
In the same way `d^s∘a∘d^-s = a^(n_4^s)` with `s = ord(d)` gives `ord(a) | 2^(v2(3^(m_d s) - 1))`,
and `v2(3^(m_d s) - 1) <= v2(m_d) + gamma(m_b) + v2(m_c) + 2 + 2 = cap(m)`. Since
`ord(a) = 2^k`, this gives `k <= cap(m)`. This does not use the relation for `n_1`, which holds
trivially for `b = 1`. ∎

**Item 1, construction.** Fix `k <= cap(m)` and put `N = 2^k`, `a(x) = x + 1`, `b = 1`,
`d(x) = 3^(m_d) x`, `n_3 = 3^(m_c)`. Every `x != 0` mod `N` is `2^v u` with `0 <= v < k` and `u` a
unit mod `2^n`, `n = k - v`, uniquely determined mod `2^n`. Call this set the layer `v`. Every map
below preserves each layer. Define `c` as follows.
- On a layer with `n <= 2`, or with `n >= 3` and `m_d >= L = 2^(n-2)`, and at `x = 0`: `c = id`.
- On a layer with `n >= 3` and `m_d < L`: write `u = s 3^i` (F2). Since `m_d` and `L` are powers
  of 2, `m_d | L`. Write `i = r + m_d q` with `0 <= r < m_d` and `q mod L/m_d`. Put
  `lambda(i) = r + n_3 m_d q mod L` and `c(2^v s 3^i) = 2^v s 3^(lambda(i))`.

This `lambda` is well defined, because `q -> q + L/m_d` changes `n_3 m_d q` by `n_3 L`. It is a
bijection: on each residue `r` it is multiplication by the unit `n_3` on `q`.

*Relation `d∘a∘d^-1 = a^(n_4)`.* `d(a(d^-1 x)) = 3^(m_d)(3^(-m_d) x + 1) = x + n_4`.

*Relation `a∘b∘a^-1 = b^(n_1)`.* Both sides are `1`, for every odd `n_1`.

*Relation `c∘d∘c^-1 = d^(n_3)`, i.e. `c∘d = d^(n_3)∘c`.* On a layer where `c = id` we need
`d = d^(n_3)` there. If `n >= 3` and `m_d >= L`, then `3^(m_d) ≡ 1 mod 2^n` by (F1), since `m_d` is
even and `v2(m_d) + 2 >= n`. So `d` is the identity on the layer. If `n <= 2`, then `d` and
`d^(n_3)` multiply `u` by `3^(m_d)` and `3^(m_d n_3)`, and these agree mod 4 because `n_3` is odd.
On the other layers `d` acts on `(s, i)` by `i -> i + m_d` and `d^(n_3)` by `i -> i + n_3 m_d`.
If `i = r + m_d q`, then `i + m_d = r + m_d (q + 1)`, so `lambda(i + m_d) = lambda(i) + n_3 m_d`.
This is the relation.

*Relation `b∘c∘b^-1 = c^(n_2)`, i.e. `c^(n_2 - 1) = 1`.* On each layer with `n >= 3` and
`m_d < L`, `c^t` multiplies `q in Z/2^M` by `n_3^t`, where `M = n - 2 - v2(m_d)`. By (F1) the order
of `n_3 = 3^(m_c)` mod `2^M` is at most `max(2, 2^(M - 2 - v2(m_c)))`. This is largest on the
layer `v = 0`, where it is at most `max(2, 2^(k - 4 - v2(m_d) - v2(m_c)))`. Since
`gamma(m_b) >= 1` and `k <= cap(m)`, that is at most `2^gamma(m_b)`. So `ord(c)` divides `2^gamma(m_b)`, which divides `n_2 - 1`.

*Membership in `W_k`.* `a` and `d` are affine with odd linear part, so they preserve every
congruence mod `2^r`. For `c`, take `x ≡ x' mod 2^r` with `1 <= r <= k`. If `x` and `x'` have
different valuations, or valuation at least `r`, then both are `≡ 0 mod 2^r`, and so are their
images, since `c` preserves valuation. Otherwise `x = 2^v u`, `x' = 2^v u'` with `v < r` and
`u ≡ u' mod 2^t`, `t = r - v`. We show `c(x) ≡ c(x') mod 2^r`. If `c` is the identity on the layer, or `t = 1`, there is nothing to show. First,
`lambda(i) ≡ i mod 2`: for `m_d >= 2` because `lambda(i) ≡ r ≡ i mod m_d`, and for `m_d = 1`
because `lambda(i) = n_3 i` with `n_3` odd. So `c` preserves `s` and the parity of `i`, hence
the class `s (-1)^i` mod 4, which settles `t = 2`. For `t >= 3`, (F2) gives `s = s'` and
`i ≡ i' mod 2^(t-2)`, and we need `lambda(i) ≡ lambda(i') mod 2^(t-2)`. Put `e = t - 2`. If `e <= v2(m_d)`, then `r ≡ r' mod 2^e`,
and `lambda(i) ≡ r mod m_d`, so this holds. If `e > v2(m_d)`, then `r = r'` and
`q ≡ q' mod 2^(e - v2(m_d))`, so `lambda(i) - lambda(i') = n_3 m_d (q - q')` is `≡ 0 mod 2^e`.
A bijection of `Z/2^k` that preserves every congruence class relation is in `W_k`. ∎

So a b-trivial single-cycle model exists at every level `k <= cap(m)`. `captower.py` builds it
and checks bijectivity, membership in `W_k` and the four relations at every level `1..cap(m)`,
for the 27 tuples and the extra `n_1` listed in the target. Every case passes
(`captower-output.txt`).

**Item 2.** A b-trivial single-cycle model is a single-cycle model. ∎

**Item 3 (block lemma).** Let `(a, b, c, d)` be a single-cycle model of level `k`, with `a = x + 1`.
The relation `a∘b∘a^-1 = b^(n_1)` says that `a` normalizes `<b>`. So `a` maps `<b>`-orbits to
`<b>`-orbits: `a(<b> x) = <b^(n_1)> a(x) = <b> a(x)`, because `n_1` is odd and `<b>` is a
2-group. So the orbits of `<b>` form a system of blocks for the regular cyclic group `<a>` on
`Z/2^k`. The blocks of a regular action of `Z/2^k` are the cosets of one subgroup `2^j Z/2^k`,
which are the residue classes mod `2^j`. So there is one `j` for which every `<b>`-orbit is a
class mod `2^j`, which is the cone below a level-`j` vertex. Then `b` fixes every level-`j`
vertex, and the cyclic group `<b>` is transitive on each cone of size `2^(k-j)`. So `b` is one
`2^(k-j)`-cycle there, and `ord(b) = 2^(k-j)`. The action on the level-`j` vertices is a
homomorphism to `W_j` in which `a` acts as `x -> x + 1` mod `2^j` and `b` acts trivially. This is
a b-trivial single-cycle model of level `j`, so `j <= cap(m)` by item 1. If `j = 0`, then `b` is
level-transitive, and item 4 with `x = b`, `y = a`, `q = n_1` gives `k <= 1`. ∎

**Item 4 (rigidity lemma).** By Lemma 1 of the required route we may conjugate in `W_M` so that
`x = t : l -> l + 1`. Then `y(l + 1) = y(t(l)) = t^q(y(l)) = y(l) + q`, so `y(l) = q l + y(0)` is
affine. Suppose `M >= 2`. Then `y` induces `l -> 3 l + y(0)` on level 2, which is `Z/4`. Its square
is `l -> 9 l + 4 y(0) = l` mod 4. So `y` has order at most 2 on level 2 and is not transitive
there. This contradicts level-transitivity. ∎

**Rotation and J-restriction (the remarks in the target).** In both cases the elements listed
fix the root `v` of the cone, and the four relations follow from the original ones. For
example, with `c' = c^(2^p)` and `b` fixing `v`, `b∘c'∘b^-1 = c'^(n_2)`. Likewise,
`c'∘d'∘c'^-1 = d'^(n_3^(2^p))` for `d' = d^(2^q)`, `d'∘a'∘d'^-1 = a'^(n_4^(2^q))` for
`a' = a^(2^j)`, and `a'∘b∘a'^-1 = b^(n_1^(2^j))`. The same holds with `(a, b^(m_b), c^(m_c), d^(m_d))`
for the cone of a level-`J` vertex under `a = x + 2^J`. The element in the odometer role (`b`,
resp. `a`) is one cycle on the cone. ∎
