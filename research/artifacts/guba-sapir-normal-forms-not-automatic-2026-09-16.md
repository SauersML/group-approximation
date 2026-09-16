# The Guba–Sapir normal forms of Thompson's group F do not fellow travel

Swarm lane on `thompson-f-is-automatic`, 2026-09-16. Supports the claim
`thompson-f-guba-sapir-normal-forms-not-automatic`.

## 0. Result

Over `A = {x^±1, y^±1}` with `x = x0`, `y = x1`, let `N` be the Guba–Sapir set
of normal forms. By CGHJS (arXiv:1811.11691v1, Section 1), `N` is the set of
freely reduced words containing no subword `y^ε x^i y` (`i >= 1`) and no subword
`y^ε x^(i+1) y^-1` (`i >= 1`), where `ε = ±1`. `N` is regular, and by
Guba–Sapir's Theorem 2, as relayed by CGHJS §2.2, it is a set of unique normal
forms. The same set `N` is the normal-form set of the CGHJS autostackable
structure (CGHJS Theorem 1.1 and the remark after it).

For `L >= 1` put

    u_L = y x^L,        v_L = x^L y x^-(L+1) y x^(L+1).

**Theorem.** Both `u_L` and `v_L` lie in `N`, and `u_L y = v_L` in `F`. Take
`L >= 2`, `a = floor(L/2)`, and let `P(w)` be the vertex set
`{w(0), ..., w(|w|)}` of the path in the Cayley graph `Γ(F, A)`, where `w(t)`
is the prefix of length `t`. Then

    dist( y x^a , P(v_L) ) >= (a - 1)/2 .

So the Hausdorff distance between `P(u_L)` and `P(v_L)` tends to infinity with
`L`.

**Corollary.** Let `L_0 ⊆ A*` contain `u_L` and `v_L` for infinitely many `L`.
This covers `N` and every language containing `N`. Then `L_0` is not the
language of a synchronous or an asynchronous automatic structure for `F` over
`A`. By uniqueness of Guba–Sapir normal forms, the same holds for every
sublanguage of `N` that maps onto `F`, since such a sublanguage is `N` itself.
In particular, the normal-form set of the CGHJS autostackable structure is not
the language of a synchronous or asynchronous automatic structure.

This does not decide `thompson-f-is-automatic`. It excludes explicit candidate
languages. The main one, `N`, is regular, has uniqueness, and is not covered by
Hauze's Theorem 1.1: `|v_L| = 3L + 4` while `|u_L y| <= L + 2`, so the additive excess
of `N` over geodesic length is unbounded.

§7 proves the same kind of result for a second classical normal form over `A`,
the telescoped standard (Cannon–Floyd–Parry) normal forms `T`. Let
`s_n = x^-(n-1) y^-1 x^(n-1)` and `t_n = y x^-n y^-1 x^n`. Both lie in `T`,
`s_n y = t_n`, and `dist(x^-(n-1), P(t_n)) >= (n - 2)/2` (Proposition 7.1). So
no language containing infinitely many of these pairs, `T` in particular, is
the language of a synchronous or asynchronous automatic structure over `A`
(Corollary 7.2).

## 1. Conventions

**Maps.** Let `X0, X1` be the piecewise linear homeomorphisms of `[0,1]`

    X0(t) = t/2 on [0,1/2],   t - 1/4 on [1/2,3/4],   2t - 1 on [3/4,1];
    X1(t) = t on [0,1/2],     t/2 + 1/4 on [1/2,3/4], t - 1/8 on [3/4,7/8],  2t - 1 on [7/8,1].

A word `s1 s2 ... sk` over `A` is sent to the composite `s1 ∘ s2 ∘ ... ∘ sk`,
with `x ↦ X0` and `y ↦ X1`. So the group product `gh` is the map `g ∘ h`, and
right multiplication by a letter is precomposition.

**This is a homomorphism `ρ` from `F`.** `F` has the presentation
`⟨x, y | [x y^-1, x^-1 y x], [x y^-1, x^-2 y x^2]⟩` (Cannon–Floyd–Parry,
*Introductory notes on Richard Thompson's groups*, 1996). The map
`X0 ∘ X1^-1` is the identity on `[3/4, 1]`: there `X1^-1(t) = (t+1)/2` lies in
`[7/8, 1]`, where `X0(s) = 2s - 1`. Conjugation `g ∘ f ∘ g^-1` has support
`g(supp f)`. Hence `ρ(x^-1 y x)` and `ρ(x^-2 y x^2)` are supported in
`X0^-1([1/2,1]) = [3/4,1]` and `X0^-2([1/2,1]) = [7/8,1]`, so both relators map
to the identity.

Every bound below has the form `|h|_A >= φ(ρ(h))`. It is proven by applying
`ρ` to an arbitrary word for `h`, so injectivity of `ρ` is never used.

**Breakpoints and depth.** For an increasing PL homeomorphism `f` of `[0,1]`,
`bp(f) ⊂ (0,1)` is the set of points where `f` is not differentiable. A
dyadic rational `p = k/2^n` with `k` odd has `depth(p) = n`. Put
`D(f) = max{depth(p) : p ∈ bp(f)}`, with `D(f) = 0` if `bp(f)` is empty. Every
element of `ρ(F)` has dyadic breakpoints.

**Slope at 0.** `α(f) = log2 f'(0+)`. Since `f(0) = 0`, `α` is a homomorphism,
with `α(X0) = -1` and `α(X1) = 0`. Hence `α(ρ(w)) = -(x-exponent sum of w)` and

    |h|_A >= |α(ρ(h))|.                                                (1.1)

**Two families of conjugates.** For `n, m >= 1` put

    x_n = x^-(n-1) y x^(n-1),        z_m = x^m y x^-m.

We use the following one-sided slope rule. If `f` fixes `p` with one-sided
slopes `(f'(p-), f'(p+))` and `g` is an increasing PL homeomorphism, then
`g ∘ f ∘ g^-1` fixes `g(p)` with the same one-sided slopes. The reason is that
`(g∘f∘g^-1)'(g(p)±) = g'(p±) f'(p±) (g^-1)'(g(p)±)`, and
`g'(p±) (g^-1)'(g(p)±) = 1`.

`X1` is the identity on `[0,1/2]` and has slopes `(1, 1/2)` at `1/2`. We have
`X0^-(n-1)(1/2) = 1 - 2^-n` and `X0^m(1/2) = 2^-(m+1)` (see (P3), (P4) below).
Therefore:

- `ρ(x_n)` is supported on `[b_n, 1]` with `b_n = 1 - 2^-n`, and has slopes
  `(1, 1/2)` at `b_n`. So `b_n ∈ bp(ρ(x_n^-1))`, and `ρ(x_n^-1)` is the identity
  on `[0, b_n]`.
- `ρ(z_m)` is supported on `[c_m, 1]` with `c_m = 2^-(m+1)`, and has slopes
  `(1, 1/2)` at `c_m`. So `c_m ∈ bp(ρ(z_m))` and `ρ(z_m)` fixes `c_m`.

**Powers of X0.** For integers `k >= 0` and `n >= 1`, directly from the formulas:

- (P1) `X0^k` is linear on `[1 - 2^-(k+1), 1]`, and `X0^-k` is linear on
  `[1/2, 1]`.
- (P2) `X0^k` is linear on `[0, 1/2]`, and `X0^-k` is linear on
  `[0, 2^-(k+1)]`.
- (P3) `X0^-k(1 - 2^-n) = 1 - 2^-(n+k)`, and `X0^k(1 - 2^-n) = 1 - 2^-(n-k)`
  when `k <= n - 1`.
- (P4) `X0^k(2^-n) = 2^-(n+k)`, and `X0^-k(2^-n) = 2^-(n-k)` when `k <= n - 1`.

For (P3) and (P4) use `X0(t) = 2t - 1` on `[3/4,1]`, `X0^-1(t) = (t+1)/2` on
`[1/2,1]`, `X0(t) = t/2` on `[0,1/2]` and `X0^-1(t) = 2t` on `[0,1/4]`, then
iterate. The side conditions keep every intermediate point inside the interval
where the formula is used.

**The relation `u_L y = v_L`.** In `F` we have `y x^L y = x^L y x^-(L+1) y x^(L+1)`.
Multiplying on the left by `y^-1 x^-L`, this is equivalent to
`x_1^-1 x_(L+1) x_1 = x_(L+2)`, with `x_n` as defined above. It is also the
size-`L` `y`-rule of `Σ` with `ε = 1` (CGHJS §2.2). We derive it from the
two-relator presentation, so it holds in `F` and not only in `ρ(F)`.

- With `[a,b] = a^-1 b^-1 a b`, `a = x y^-1` and `x^-1 y x = x_2`, the first
  relator says `a^-1 x_2 a = x_2`. Since `a^-1 = y x^-1` and
  `x^-1 x_n x = x_(n+1)` (immediate from the definition), this reads
  `y x_3 y^-1 = x_2`, that is `x_1^-1 x_2 x_1 = x_3`. The second relator is
  `[a, x_3]` and gives `x_1^-1 x_3 x_1 = x_4` in the same way.
- Conjugating by `x^(k-1)`, and using `x^-1 x_n x = x_(n+1)`, gives
  `x_k^-1 x_(k+1) x_k = x_(k+2)` and `x_k^-1 x_(k+2) x_k = x_(k+3)` for all
  `k >= 1`.
- Induction on `n >= 2` shows `x_1^-1 x_n x_1 = x_(n+1)`. The cases `n = 2, 3`
  are above. For `n >= 3`, `x_(n+1) = x_(n-1)^-1 x_n x_(n-1)`, so conjugating
  by `x_1` and using the cases `n - 1` and `n` gives
  `x_1^-1 x_(n+1) x_1 = x_n^-1 x_(n+1) x_n = x_(n+2)`.

`ρ(u_L) ∘ X1 = ρ(v_L)` was also confirmed in exact arithmetic for `L <= 30`
(§8).

**Membership.** `u_L = y x^L` is freely reduced and contains no `y` after a
positive power of `x`. `v_L = x^L y x^-(L+1) y x^(L+1)` is freely reduced. Its
only subwords of the form `y^ε x^i y^δ` are `y x^-(L+1) y`, which has a negative
exponent, so neither forbidden pattern occurs. Hence `u_L, v_L ∈ N`.

## 2. The depth lemma

**Lemma A.** For every `h ∈ F`, `|h|_A >= D(ρ(h)) - 2`.

*Proof.* For increasing PL homeomorphisms `f, g`,

    bp(f ∘ g) ⊆ bp(g) ∪ g^-1(bp(f)),                                   (2.1)

because `f ∘ g` is linear near `t` whenever `g` is linear near `t` and `f` is
linear near `g(t)`.

The four maps `X0^±1, X1^±1` have breakpoint sets `{1/2, 3/4}`, `{1/4, 1/2}`,
`{1/2, 3/4, 7/8}` and `{1/2, 5/8, 3/4}`, all of depth at most `3`. Each of the
four maps is, on each of its pieces, `t ↦ 2^e t + d` with `e ∈ {-1, 0, 1}` and
`d ∈ (1/8)Z`:

- `X0`: `t/2`, `t - 1/4`, `2t - 1`;
- `X0^-1`: `2t`, `t + 1/4`, `(t+1)/2`;
- `X1`: `t`, `t/2 + 1/4`, `t - 1/8`, `2t - 1`;
- `X1^-1`: `t`, `2t - 1/2`, `t + 1/8`, `(t+1)/2`.

The four inverses `s^-1` are again among these maps. So for dyadic
`p ∈ (0,1)`,

    depth(s^-1(p)) <= max(depth(p) + 1, 3).                             (2.2)

Let `w = s1 ... sk` be any word for `h`, and put `h_i = ρ(s1 ... si)`, so
`h_i = h_(i-1) ∘ ρ(s_i)`. By (2.1) and (2.2),
`D(h_i) <= max(3, D(h_(i-1)) + 1)`. Since `D(h_0) = 0`, induction gives
`D(h_i) <= i + 2` for `i >= 1`. Taking `w` geodesic gives
`D(ρ(h)) <= |h|_A + 2` when `h ≠ 1`. The case `h = 1` is trivial. ∎

Applied to `h^-1`, the lemma also bounds the depth of breakpoints in the range,
though that is not needed below. Spot check: exhaustive on the ball of radius 8
(11,237 elements), with no violation of Lemma A, of its range version, or of
(1.1). The computed sphere sizes are `1, 4, 12, 36, 108, 314, 906, 2576, 7280`.
Equality in Lemma A occurs, so the constant `2` is sharp (§8).

## 3. Breakpoints pulled back through powers of x0

We use two elementary facts about composites. Let `f, g` be increasing PL
homeomorphisms and `t ∈ (0,1)`.

- (C1) If `g` is linear near `t` and `g(t) ∈ bp(f)`, then `t ∈ bp(f ∘ g)`.
- (C2) If `t ∈ bp(g)` and `f` is linear near `g(t)`, then `t ∈ bp(f ∘ g)`.

In both cases the two one-sided slopes of `f ∘ g` at `t` are a common nonzero
factor times two different numbers.

**Lemma B (near 1).** Let `a >= 1` and `j >= 1`. Then

    D( ρ(x_(a+1)^-1 x^(j-a)) ) >= j + 1.

*Proof.* Put `f = ρ(x_(a+1)^-1)`. By §1, `b = 1 - 2^-(a+1)` lies in `bp(f)`.
Put `k = j - a`, `s = X0^k` and `c = 1 - 2^-(j+1)`, a point of depth `j + 1`.
By (C1) it suffices to show that `s(c) = b` and that `s` is linear near `c`.

- If `k >= 0`: `c = 1 - 2^-(a+1+k)`. By (P3) with `n = a + 1 + k` we get
  `X0^k(c) = 1 - 2^-(a+1) = b`, and `k <= n - 1` holds. By (P1), `X0^k` is
  linear on `[1 - 2^-(k+1), 1]`, which contains `c` in its interior because
  `a >= 1`.
- If `k = -r < 0`: then `1 <= r <= a - 1`, since `j >= 1`. By (P3),
  `X0^-r(c) = 1 - 2^-(j+1+r) = b`. By (P1), `X0^-r` is linear on `[1/2, 1]`,
  whose interior contains `c >= 3/4`. ∎

**Lemma C (near 0).** Let `m >= 1`, and let `f` be an increasing PL
homeomorphism with `c_m = 2^-(m+1) ∈ bp(f)`. Then for every `j >= 1`,

    D( f ∘ X0^(m-j) ) >= j + 1.

*Proof.* Put `k = m - j` and `c = 2^-(j+1)`, a point of depth `j + 1`. By (C1)
it suffices to show that `X0^k(c) = c_m` and that `X0^k` is linear near `c`.

- If `k >= 0`: by (P4), `X0^k(2^-(j+1)) = 2^-(j+1+k) = 2^-(m+1)`. By (P2),
  `X0^k` is linear on `[0, 1/2]`, whose interior contains `c <= 1/4`.
- If `k = -r < 0`: `r = j - m <= j - 1`. By (P4) with `n = j + 1`,
  `X0^-r(c) = 2^-(j+1-r) = 2^-(m+1)`. By (P2), `X0^-r` is linear on
  `[0, 2^-(r+1)]`, whose interior contains `c = 2^-(j+1)` because `j > r`. ∎

**The two maps to which Lemma C is applied.** Let `a, m >= 1`.

- `f_B = ρ(x_(a+1)^-1 z_m) = ρ(x_(a+1)^-1) ∘ ρ(z_m)`. Here `c_m ∈ bp(ρ(z_m))`,
  and `ρ(z_m)` fixes `c_m <= 1/4`. Near `c_m`, `ρ(x_(a+1)^-1)` is the identity,
  since its support is `[1 - 2^-(a+1), 1] ⊆ [3/4, 1]`. By (C2),
  `c_m ∈ bp(f_B)`.
- `f_C = ρ(x_(a+1)^-1 z_m x_(a+2)) = f_B ∘ ρ(x_(a+2))`. `ρ(x_(a+2))` is the
  identity near `c_m`, since its support is `[1 - 2^-(a+2), 1]`. By (C1),
  `c_m ∈ bp(f_C)`.

## 4. Automatic structures give bounded Hausdorff distance

We follow Epstein et al., *Word Processing in Groups* (1992). Synchronous
structures are in Chapter 2 and asynchronous ones in Chapter 7; section and
theorem numbers were not re-verified this session.

A synchronous or asynchronous automatic structure for `G` over `A` consists of:

- a finite-state acceptor `W` whose language `L(W)` maps onto `G`;
- for each `a ∈ A`, a two-tape automaton `M_a` accepting exactly the pairs
  `(u, v)` with `u, v ∈ L(W)` and `ū a = v̄`.

In the synchronous case `M_a` reads padded pairs. In the asynchronous case each
state reads from one designated tape, and each tape ends with an end marker.

**Lemma D.** Given such a structure, there is `K` with the following property.
For all `a ∈ A` and all `u, v ∈ L(W)` with `ū a = v̄`, every vertex of `P(u)` is
within distance `K` of `P(v)`, and every vertex of `P(v)` is within distance `K`
of `P(u)`.

*Proof.* This is the standard fellow-traveller argument, in the form needed
here. Fix `a` and consider the finite directed graph `V_a` described below.

- A vertex is a triple `(state of M_a, e1, e2)`, where the flag `e_i ∈ {0,1}`
  records whether the end marker of tape `i` has been read. The flags are
  unnecessary in the synchronous case, where every accepted string is a valid
  padded pair by definition.
- An edge is a transition of `M_a` that respects the flags: no letter of tape
  `i` is read after its end marker.

An *initial vertex* is `(initial state, 0, 0)`. An *accepting vertex* is
`(accept state, 1, 1)`, or just an accept state in the synchronous case. Any
path in `V_a` from an initial vertex to an accepting vertex spells an input
accepted by `M_a`. Such an input is a pair `(u', v')` with `u', v' ∈ L(W)` and
`ū' a = v̄'`.

For each vertex `q` from which an accepting vertex is reachable, fix a shortest
such path. It has fewer than `|V_a|` edges. Let `p_q` and `r_q` be the words it
reads on tapes 1 and 2, with end markers and padding symbols removed. Each edge
reads at most one symbol from each tape, so `|p_q| + |r_q| <= 2|V_a|`.

Take an accepting run on `(u, v)`. Suppose that at some moment the run is at
vertex `q` and has consumed the prefixes `u(..t)` and `v(..t')`. Following the
run up to that moment and then the fixed path from `q` gives an accepting run
on `(u(..t) p_q, v(..t') r_q)`. Hence `(u(..t) p_q)‾ a = (v(..t') r_q)‾`, so

    d(u(t), v(t')) = |p̄_q a r̄_q^-1| <= |p_q| + 1 + |r_q| <= 2|V_a| + 1.

Along the run each head advances one symbol at a time from position `0` to the
end. So every `t ∈ [0, |u|]` occurs together with some `t'`, and every `t'`
together with some `t`. Take `K = 2 max_a |V_a| + 1`. ∎

Two details of the step "following the run and then the fixed path". A run
that has already read an end marker only continues along edges that respect
the flag, so the concatenated input is again a pair of strings with end
markers. In the synchronous case the concatenation is accepted by `M_a`, so by
definition it is a padded pair, and removing padding gives
`(u(..t) p_q, v(..t') r_q)`.

In particular, `sup_L dist(P(u_L), P(v_L)) = ∞` forbids both kinds of
automatic structure whose language contains infinitely many of the pairs
`(u_L, v_L)`, since `u_L y = v_L`.

## 5. Proof of the Theorem

Membership and the relation `u_L y = v_L` were shown in §1. Fix `L >= 2`, and
put `a = floor(L/2)` and `m = L - a`. Then `1 <= a <= m`. The vertex
`p = y x^a` is the prefix of `u_L` of length `a + 1 <= L + 1`, so `p ∈ P(u_L)`.
For `q ∈ F` we have `d(p, q) = |p^-1 q|_A`, and `p^-1 = x^-a y^-1`. Note that
`x_(a+1)^-1 = x^-a y^-1 x^a`.

The word `v_L = x^L y x^-(L+1) y x^(L+1)` has length `3L + 4`. Its prefixes
fall into three segments.

**Segment A: `q = x^j` with `0 <= j <= L`.** Here

    p^-1 q = x^-a y^-1 x^a · x^(j-a) = x_(a+1)^-1 x^(j-a).

The `x`-exponent sum is `j - a`, so by (1.1) `|p^-1 q| >= |a - j|`. For
`j >= 1`, Lemma B gives `D(ρ(p^-1 q)) >= j + 1`, so by Lemma A
`|p^-1 q| >= j - 1`. Hence:

- for `j = 0`: `|p^-1 q| >= a`;
- for `1 <= j <= a`: `|p^-1 q| >= max(a - j, j - 1) >= ((a - j) + (j - 1))/2 = (a - 1)/2`;
- for `j > a`: `|p^-1 q| >= j - 1 >= a`.

**Segment B: `q = x^L y x^-j` with `0 <= j <= L + 1`.** Write `x^L = x^a x^m`.
Then

    p^-1 q = (x^-a y^-1 x^a)(x^m y x^-m) x^(m-j) = x_(a+1)^-1 z_m x^(m-j),

so `ρ(p^-1 q) = f_B ∘ X0^(m-j)`, with `f_B` as in §3. The `x`-exponent sum is
`m - j`, so `|p^-1 q| >= |m - j|`. For `j >= 1`, Lemma C applied to
`f = f_B`, which is allowed because `c_m ∈ bp(f_B)` (§3), gives
`D(ρ(p^-1 q)) >= j + 1`, so `|p^-1 q| >= j - 1`. Hence:

- for `j = 0`: `|p^-1 q| >= m`;
- for `1 <= j <= m`: `|p^-1 q| >= (m - 1)/2`;
- for `j > m`: `|p^-1 q| >= j - 1 >= m`.

**Segment C: `q = x^L y x^-(L+1) y x^j` with `0 <= j <= L + 1`.** Since
`m - (L + 1) = -(a + 1)`,

    p^-1 q = x_(a+1)^-1 z_m · x^-(a+1) y x^(a+1) · x^(j-a-1) = x_(a+1)^-1 z_m x_(a+2) x^(j-a-1).

Put `j' = L + 1 - j`, so `j - a - 1 = m - j'`. Then
`ρ(p^-1 q) = f_C ∘ X0^(m-j')`. The `x`-exponent sum is `j - a - 1`, so
`|p^-1 q| >= |a + 1 - j|`. For `j <= L`, that is `j' >= 1`, Lemma C applied to
`f = f_C`, allowed because `c_m ∈ bp(f_C)` (§3), gives
`D(ρ(p^-1 q)) >= j' + 1 = L + 2 - j`, so `|p^-1 q| >= L - j`. Hence:

- for `j <= a + 1`: `|p^-1 q| >= L - j >= L - a - 1 = m - 1 >= (m - 1)/2`;
- for `a + 1 < j <= L`: `|p^-1 q| >= max(j - a - 1, L - j) >= (m - 1)/2`, since the
  two terms add up to `m - 1`;
- for `j = L + 1`: `|p^-1 q| >= |a - L| = m`.

**Conclusion.** Every vertex `q ∈ P(v_L)` satisfies
`d(p, q) >= min(a, m, (a - 1)/2, (m - 1)/2) = (a - 1)/2`, because `a <= m`.
Hence `dist(y x^a, P(v_L)) >= (a - 1)/2`, and the Hausdorff distance between
`P(u_L)` and `P(v_L)` is at least `(floor(L/2) - 1)/2`. ∎

**Remarks on the proof.**

- Segments A, B and C are the prefixes of lengths `0..L`, `L+1..2L+2` and
  `2L+3..3L+4`. Together they are all `3L + 5` vertices of `P(v_L)`.
- The proof uses only that `ρ` is a homomorphism (§1), together with (1.1),
  Lemma A, Lemma B, Lemma C and the elementary facts (P1)–(P4), (C1), (C2).
- The bound is not sharp. The computation in §8 finds the exact value
  `dist(y x^a, P(v_L)) = a + 1` for `4 <= L <= 15`.
- A fixed time gives the synchronous failure more directly. The prefixes of
  length `L` are `y x^(L-1)` and `x^L`, and `(y x^(L-1))^-1 x^L = x_L^-1 x`.
  Lemma B with its parameters set to `a = L - 1` and `j = L` gives
  `D(ρ(x_L^-1 x)) >= L + 1`. So `|x_L^-1 x| >= L - 1`. The Hausdorff statement
  is what also excludes asynchronous structures.

## 6. Proof of the Corollary, and scope

**Proof of the Corollary.** Suppose `L_0` is the language `L(W)` of a
synchronous or asynchronous automatic structure for `F` over `A`, and that
`u_L, v_L ∈ L_0` for all `L` in an infinite set `S`. Let `K` be the constant
of Lemma D, and apply the lemma with the letter `y` to the pairs `(u_L, v_L)`,
`L ∈ S`. Since `u_L y = v_L` in `F`, every vertex of `P(u_L)`, and in
particular `y x^floor(L/2)`, is within distance `K` of `P(v_L)`. The Theorem
gives `dist(y x^floor(L/2), P(v_L)) >= (floor(L/2) - 1)/2`, which exceeds `K`
for large `L ∈ S`. This is a contradiction.

`N` contains every `u_L` and `v_L` by §1, so the Corollary applies to `N` and to
every language containing `N`.

For sublanguages we need Guba–Sapir's uniqueness theorem ([GS97, Theorem 2], as
relayed by CGHJS §2.2; [GS97] itself was not fetched this session): distinct words of `N`
represent distinct elements of `F`. Granting it, a sublanguage `L_1 ⊆ N` that
maps onto `F` must contain, for each `g ∈ F`, the unique word of `N`
representing `g`. So `L_1 = N`. This is the only place where uniqueness is
used. §8 records a finite check: the `48,931` words of `N` of length at most
`10` have pairwise distinct images under `ρ`, so they represent distinct
elements of `F`. That check is evidence only.

**Hausdorff-close languages.** The proof is robust in the following form. Let
`L_2` be the language of a synchronous or asynchronous automatic structure for
`F` over `A`. Suppose there are a constant `C` and an infinite set `S` such
that for each `L ∈ S` the language `L_2` contains words `u'_L`, `v'_L` with
`ū'_L = ū_L` and `v̄'_L = v̄_L`, whose paths satisfy
`d_H(P(u'_L), P(u_L)) <= C` and `d_H(P(v'_L), P(v_L)) <= C`. Here `d_H` is the
Hausdorff distance between vertex sets of `Γ(F, A)`. Then `u'_L y = v'_L` in
`F`, and by the triangle inequality for `d_H`,

    d_H(P(u'_L), P(v'_L)) >= (floor(L/2) - 1)/2 - 2C.

This contradicts Lemma D for large `L ∈ S`. So no automatic structure over `A`
can have words that uniformly shadow the Guba–Sapir normal forms along the
family `u_L`, `v_L`.

**Scope.**

- Nothing here decides `thompson-f-is-automatic`. It rules out explicit
  candidate languages. The first is the regular language `N`, which has
  uniqueness and labels the spanning tree of the CGHJS autostackable structure.
  The second is the language `T` of §7.
- The alphabet is fixed to `A = {x0^±1, x1^±1}`. Automaticity does not depend
  on the finite generating set, but a specific language is tied to its
  alphabet. Over another generating set, the analogue would have to be stated
  for an image of `N` under a substitution, and this is not done here.
- Hauze's Theorem 1.1 (arXiv:1801.01965, fetched 2026-09-16) concerns a
  language `L` over `A` with a constant `c` such that "for every element
  `g ∈ F` there is a single word `w ∈ L` such that `w` represents `g` and
  `|w| <= |g|_X + c`". It shows such an `L` "cannot be a subset of the language
  associated with an automatic structure for `F`". `N` has no such constant:
  `|v_L| = 3L + 4`, while `|v̄_L| = |ū_L y| <= L + 2`. So `N` is not covered by
  Hauze's result, and the obstruction here is of a different kind. It exhibits
  an explicit pair of normal forms whose paths diverge. Hauze's argument
  instead analyses the accepted near-geodesic representatives of specific
  elements `f_k`, `g_k` (Hauze, Chapter 4).
- The notion excluded is anything that forces bounded Hausdorff distance
  between the paths of accepted `u` and `v` with `ū a = v̄`. This includes both
  standard automatic notions, by Lemma D. It does not concern weaker
  properties such as autostackability, which CGHJS prove for this same `N`.

## 7. Telescoped standard normal forms

This section proves a second, independent obstruction of the same kind, for
the standard normal forms. It also corrects one sentence of
`research/artifacts/zp-thompson-f-automatic-2026-09-13.md`. It supports the
claim `thompson-f-standard-normal-forms-not-automatic`. Nothing in §0–§6
depends on it.

**Standard normal forms.** Use the infinite generators `x_0 = x` and
`x_n = x^-(n-1) y x^(n-1)` for `n >= 1`, as in §1. A *standard normal form* is
a word

    x_0^(b_0) x_1^(b_1) ... x_r^(b_r) x_r^-(c_r) ... x_1^-(c_1) x_0^-(c_0)

with `b_i, c_i >= 0` that satisfies the reducedness condition: if `b_i > 0` and
`c_i > 0`, then `b_(i+1) > 0` or `c_(i+1) > 0`. By CFP 1996 (§2; not re-fetched
this session), every element of `F` has exactly one standard normal form. The
*telescoped standard normal form* (TSNF) is the word over `A` obtained by
substituting `x_n ↦ x^-(n-1) y x^(n-1)` and freely reducing. Let `T ⊆ A*` be
the set of TSNFs. Only membership of two explicit words in `T` is used below;
uniqueness is not.

**Correction on `x0`.** The zp artifact says that right multiplication by `x0`
"rewrites indices along the whole word". That is true over the infinite
alphabet. After telescoping, the TSNF of `g x0` is the free reduction of
`TSNF(g) · x`. Write `σ` for the index shift `x_k ↦ x_(k+1)` on words in
`x_1, x_2, ...`. The relations `x_0^-1 x_k x_0 = x_(k+1)` for `k >= 1` give
`subst(σW) = x^-1 subst(W) x`.

- If `c_0 > 0`, the normal form of `g x_0` has `c_0 - 1` in place of `c_0`. The
  condition at index `0` still holds or becomes vacuous.
- If `c_0 = 0`, write `g = x_0^(b_0) W` with `W` in `x_1, x_2, ...`. Then
  `g x_0 = x_0^(b_0 + 1) σW`, which is again a normal form: index `1` is empty,
  the conditions at higher indices shift, and the one at index `0` is vacuous.
  Its substitution is `x^(b_0+1) x^-1 subst(W) x`.

In both cases the substituted word is `subst(NF(g)) · x` up to free reduction.
So the multiplier `x0` moves the end of a TSNF path by one edge. Since
`(u, v)` with `ū x^-1 = v̄` is the same as `(v, u)` with `v̄ x = ū`, the
multiplier `x0` causes no fellow-travelling problem for `T`.

**Proposition 7.1.** For `n >= 2` put

    s_n = x^-(n-1) y^-1 x^(n-1),        t_n = y x^-n y^-1 x^n.

Then `s_n, t_n ∈ T` and `s_n y = t_n` in `F`. For `1 <= k <= n - 1`,

    dist( x^-k , P(t_n) ) >= (k - 1)/2 .

In particular `dist(x^-(n-1), P(t_n)) >= (n - 2)/2`, and `x^-(n-1)` is a vertex
of `P(s_n)`.

**Corollary 7.2.** No language over `A` that contains `s_n` and `t_n` for
infinitely many `n` is the language of a synchronous or asynchronous automatic
structure for `F` over `A`. This applies to `T` and to every language
containing `T`.

*Proof of 7.2.* Lemma D and Proposition 7.1, exactly as in §6. ∎

*Proof of 7.1.* `x_n^-1` is a standard normal form, and so is `x_1 x_(n+1)^-1`
(`b_1 = 1`, `c_(n+1) = 1`, all else `0`). Their substitutions `s_n` and `t_n`
are freely reduced, so `s_n, t_n ∈ T`. The relation `x_1^-1 x_n x_1 = x_(n+1)`
for `n >= 2` was derived in §1 from the presentation. It gives
`x_n^-1 x_1 = x_1 x_(n+1)^-1`, that is `s_n y = t_n`.

Fix `1 <= k <= n - 1` and put `p = x^-k`, so `p^-1 = x^k`. The word `t_n` has
length `2n + 2`. The vertices of `P(t_n)` are:

- `q = 1`;
- `q = y x^-j` for `0 <= j <= n` (family (i));
- `q = y x^-n y^-1 x^j` for `0 <= j <= n` (family (ii)).

**`q = 1`.** `p^-1 q = x^k`, so `|p^-1 q| >= k` by (1.1).

**Family (i).** `p^-1 q = x^k y x^-j = z_k x^(k-j)`, with `x`-exponent sum
`k - j`. So `|p^-1 q| >= |k - j|`, which is `k` when `j = 0`. For `j >= 1`,
Lemma C with `m = k` and `f = ρ(z_k)` applies, since `c_k ∈ bp(ρ(z_k))` by §1.
It gives `D(ρ(p^-1 q)) >= j + 1`, so `|p^-1 q| >= j - 1`. Hence:

- for `1 <= j <= k`: `|p^-1 q| >= max(k - j, j - 1) >= (k - 1)/2`;
- for `j > k`: `|p^-1 q| >= j - 1 >= k`.

**Family (ii).** Since `x^-n = x^-k x^-(n-k)`,

    p^-1 q = x^k y x^-k · x^-(n-k) y^-1 x^(n-k) · x^(j-n+k) = z_k x_(n-k+1)^-1 x^(j-n+k).

The `x`-exponent sum is `j - n + k`, so `|p^-1 q| >= |n - k - j|`. Put
`f_T = ρ(z_k) ∘ ρ(x_(n-k+1)^-1)`. Since `n - k + 1 >= 2`, the map
`ρ(x_(n-k+1)^-1)` is the identity on `[0, 3/4]`, which contains `c_k`. By
(C1), `c_k ∈ bp(f_T)`. Now `ρ(p^-1 q) = f_T ∘ X0^(k - j')` with `j' = n - j`.
For `j <= n - 1`, Lemma C with `m = k` and `j' >= 1` gives
`D(ρ(p^-1 q)) >= n - j + 1`, so `|p^-1 q| >= n - j - 1`. Hence:

- for `0 <= j <= n - k`: `|p^-1 q| >= n - j - 1 >= k - 1`;
- for `n - k < j <= n - 1`: `|p^-1 q| >= max(j - n + k, n - j - 1) >= (k - 1)/2`,
  since the two terms add up to `k - 1`;
- for `j = n`: `|p^-1 q| >= k`.

Every vertex `q` of `P(t_n)` therefore has `d(p, q) >= (k - 1)/2`. ∎

**Remarks.**

- The synchronous failure is visible at time `n - 1`. The prefixes are
  `x^-(n-1)` and `y x^-(n-2)`, whose difference is `z_(n-1) x`. Lemma C gives
  `D >= n - 1`, so they are at distance at least `n - 3`.
- `t_n = y · s_(n+1)`, so `P(t_n)` is `{1}` together with the left translate
  `y · P(s_(n+1))`, and `P(s_(n+1))` shadows `P(s_n)`. One might therefore
  expect `P(s_n)` and `P(t_n)` to be Hausdorff close. They are not, because a
  left translate is not close to the original path:
  `d(w(t), y w(t)) = |w(t)^-1 y w(t)|`, which is unbounded along `w = x^-n`.
  Proposition 7.1 makes this quantitative.
- Regularity of `T` is not examined. The reducedness condition compares
  exponents at equal indices in the two halves, which suggests that `T` is not
  regular, but no proof is recorded. Corollary 7.2 does not need it.

## 8. Computational record

The proofs above are complete without computation. The computations check
conventions and the specific identities and depth claims, in exact rational
arithmetic. Everything lives in `experiments/thompson-f-guba-sapir-ftp-2026-09-16/`:

- `plf.py`: PL homeomorphisms as node lists over `Fraction`, with composition,
  inverse, breakpoints, depth, `α` (log2 slope at `0`) and `β` (log2 slope at
  `1`). A word `s1 ... sk` is the map `s1 ∘ ... ∘ sk`, as in §1.
- `check_witnesses.py`, run as `timeout 600 python3 -B check_witnesses.py 30 8 10`.
  The output is in `check_witnesses_output.txt`: `TOTAL FAILURES: 0`, exit `0`.
- `check_tsnf.py`, run as `timeout 600 python3 -B check_tsnf.py 30 12`. The
  output is in `check_tsnf_output.txt`: `TOTAL FAILURES: 0`, exit `0`.

**`check_witnesses.py`.** Every item below is an assertion unless it is
described as reported.

- Part 0: both CFP relators map to the identity. The Guba–Sapir `y`- and
  `y^-1`-rules of sizes `1..6`, with `ε = ±1`, hold as map identities. The left
  end of the support of `ρ(x_n)` is `1 - 2^-n`, and that of `ρ(z_m)` is
  `2^-(m+1)`, for `n, m <= 7`.
- Part 1: for `1 <= L <= 30`, `u_L, v_L ∈ N` (a regular-expression test for the
  forbidden subwords) and `ρ(u_L) ∘ X1 = ρ(v_L)`.
- Part 2: for `4 <= L <= 30`, at every vertex of `P(v_L)`, the `α` values and
  the depth bounds used in segments A, B and C of §5. The minimum over `q` of
  `LB(p^-1 q)`, with `LB = max(|α|, |β|, D_dom - 2, D_ran - 2)`, is at least
  `(a - 1)/2`. The reported minima are `2, 3, 3, 4, 4, ..., 15, 15`, that is
  `m = L - a`. Also, for `3 <= L <= 30`, the synchronous difference at time `L`
  is `x_L^-1 x` with `D >= L + 1`.
- Part 3: breadth-first search on the ball of radius `8`, where BFS distance is
  exact word length. The reported sphere sizes are
  `1, 4, 12, 36, 108, 314, 906, 2576, 7280`, so `11,237` elements. `|h| >= LB(h)`
  holds at every element. `1,004` elements satisfy
  `|h| = max(D_dom, D_ran) - 2`, so the constant in Lemma A is attained.
- Part 4 (reported): exact distances `d(y x^a, q)` from the ball. For
  `4 <= L <= 15` the minimum over `q ∈ P(v_L)` is `a + 1`. The vertices outside
  the ball have distance `>= 9 > a + 1`, so this minimum is exact. For `L = 16`
  every `q` lies outside the ball, so the distance is `>= 9 = a + 1`.
- Part 5: for `3 <= n <= 30`, the synchronous TSNF example of §7:
  `s_n y = t_n`, the difference at time `n - 1` is `z_(n-1) x`, and `D >= n - 1`.
- Part 6 (evidence only): the `48,931` words of `N` of length `<= 10` have
  pairwise distinct images under `ρ`.

**`check_tsnf.py`.** For `3 <= n <= 30` it asserts `ρ(s_n) ∘ X1 = ρ(t_n)`. It
then takes `k = n - 1`, and every `1 <= k <= n - 1` when `n <= 12`, and asserts
at every vertex of `P(t_n)`:

- the `α` values `j - k` in family (i) and `n - k - j` in family (ii);
- `D_dom >= j + 1` in family (i) for `j >= 1`;
- `D_dom >= n - j + 1` in family (ii) for `j <= n - 1`;
- `min_q LB(x^k q) >= (k - 1)/2`.

The reported minima for `k = n - 1` are `n - 1`, against the proven `(n - 2)/2`.

A first draft of `check_tsnf.py` asserted a wrong `x`-exponent in family (ii):
`x^(j-k)` instead of `x^(j-n+k)`. It failed at once. The formula in §7 is the
corrected one, and it passes.

Wall-clock times were `5m12s` and `30s` on a shared machine, with CPU times
`43s` and `4.7s`.

## 9. References

Only the items marked "fetched" were read this session (2026-09-16).

- [CGHJS] N. Corwin, G. Golan, S. Hermiller, A. Johnson, Z. Šunić,
  *Autostackability of Thompson's group F*, arXiv:1811.11691v1 (2018).
  Fetched. Used: Section 1 (definition of `N` and the display of the forbidden
  subwords), Theorem 1.1 and the remark after it (same normal forms), §2.2
  (the rewriting system `Σ`, Lemma 2.2). Abstract: "it remains unknown whether
  F is automatic".
- [GS97] V. S. Guba, M. Sapir, *The Dehn function and a regular set of normal
  forms for R. Thompson's group F*, J. Austral. Math. Soc. Ser. A 62 (1997),
  315–328. Not fetched. Cited only through CGHJS §2.2, as "[10, Theorem 2]".
- [Hauze] D. Hauze, dissertation (2017), arXiv:1801.01965. Fetched. Used:
  Theorem 1.1, quoted in §6.
- [CFP] J. W. Cannon, W. J. Floyd, W. R. Parry, *Introductory notes on Richard
  Thompson's groups*, Enseign. Math. 42 (1996). Not re-fetched. Used: the
  two-relator presentation of `F`, from which §1 derives the relations it needs,
  and the definition of the standard normal form. The relators and relations
  used are also checked as map identities in §8 (parts 0 and 1, and
  `check_tsnf.py`).
- [ECHLPT] D. B. A. Epstein, J. W. Cannon, D. F. Holt, S. V. F. Levy,
  M. S. Paterson, W. P. Thurston, *Word Processing in Groups*, Jones and
  Bartlett (1992). Not re-fetched. Used: the definitions of synchronous and
  asynchronous automatic structures, recalled in §4. Lemma D is proved here from
  those definitions.
