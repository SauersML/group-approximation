# Houghton groups with at least six rays: halving pours, far commutation k^2 log k, and Dehn function x^8 log x

Lane swarm-0917-w4-pull-z-5, 2026-09-17. Zaremsky Problem 1.24. Status: complete
proof, unreviewed.

## 0. Conventions and presentation

`Y = [n] x N`, `N = {1,2,...}`, `n >= 6`. As in Lee (arXiv:1212.0257, §2) and
in `research/artifacts/zp-houghton-dehn-2026-09-13-part1.md`, permutations act on
the right and words are read left to right (`xy` = first `x`, then `y`). Also
`x^h = h^(-1) x h`, so `supp(x^h) = supp(x)·h`.

For distinct rays `x,y`, `λ_(x,y)` (written `λ_xy`) pulls ray `x` inward and
pushes ray `y` outward: `(x,p) -> (x,p-1)` for `p >= 2`, `(x,1) -> (y,1)`,
`(y,p) -> (y,p+1)`, and the identity elsewhere. So `λ_yx = λ_xy^(-1)`. Put
`τ_x = ((x,1),(x,2))`.

The *ray support* of a letter is `{x,y}` for `λ_xy` and `{x}` for `τ_x`. Two
letters with disjoint ray supports have disjoint supports in `Y`, so they commute.

**The presentation `P`.** Its generators are Lee's `g_1,...,g_(n-1), α`, together
with `λ_xy` (all `x != y`) and `τ_x` (all `x`). Its relators are:

- Lee's finite set of relators (Lee, Theorem C);
- the defining relations `λ_(1,b) = g_(b-1)`, `λ_(a,b) = g_(a-1)^(-1) g_(b-1)`,
  `τ_1 = α`, and `τ_x = u_x` for a fixed Lee word `u_x`;
- the finite set `Q` of all words of length `<= 40` in the letters
  `λ_xy^(±1), τ_x^(±1)` that are trivial in `H_n`;
- the finitely many sorting relations `g_i^ε g_j^η = g_j^η g_i^ε v_(i,ε,j,η)` of
  Lemma 3 of `research/artifacts/zp-houghton-dehn-2026-09-13-part1.md`, after
  substituting `g_(b-1) = λ_(1,b)` and `α = τ_1`.

`P` is a finite presentation of `H_n`. Mapping each new generator to its Lee word
sends every relator of `P` to a null-homotopic Lee word of bounded length. Hence
`Area_Lee(w) <= K·Area_P(w)` for every Lee word `w`, where `K` is a constant. So
upper bounds proved in `P` transfer to Lee's presentation. Below, `Area` means
`Area_P`.

Among the relators in `Q` are these:

- `[λ_xy, λ_zw]`, `[λ_xy, τ_z]`, `[τ_x, τ_z]` for disjoint ray supports;
- `λ_xy λ_yx`;
- `λ_ac λ_cb λ_bd λ_da` for distinct `a,b,c,d` (length 4). Section 1 shows it is
  trivial.
- `τ_a^(-1) λ_ab^2 τ_b λ_ba^2` (length 6). It is trivial because
  `supp(τ_b)·λ_ba^2 = {(a,2),(a,1)}`: `λ_ba` sends `(b,1) -> (a,1) -> (a,2)` and
  `(b,2) -> (b,1) -> (a,1)`.
- `τ_x^2`.

**Replacement cost.** If `u` and `v` are words equal in `H_n`, then replacing a
subword `u` by `v` inside any word costs at most `Area(u v^(-1))` relator
applications. Replacing `u^(-1)` by `v^(-1)` costs the same. Areas are invariant
under cyclic permutation, free reduction and conjugation.

**Inverse letters.** In `P`, `λ_yx` and the formal inverse `λ_xy^(-1)` are
different letters. Converting one into the other costs one relator `λ_xy λ_yx`.
Likewise `τ_x^(-1) -> τ_x` costs one relator `τ_x^2`. Below, an identity marked
"freely" may use these conversions. Each use then costs at most the number of
letters of the words involved, and these linear costs are included in every bound
stated. The only place where the exact constant matters is Lemma 1.2, and there it
is counted explicitly.

## 1. Pours

For distinct rays `a,b,c` and `m >= 0` define the word

```text
E^c_(a,b)(m) = λ_ac^m λ_cb^m          (length 2m, letters with ray support in {a,b,c}).
```

**Lemma 1.1 (the element does not depend on `c`).** As a permutation,
`E^c_(a,b)(m)` sends `(a,p) -> (b,p)` for `p <= m`, `(a,p) -> (a,p-m)` for
`p > m`, and `(b,p) -> (b,p+m)`. It fixes every other point. In particular it is
supported on rays `a,b` and does not depend on `c`. Write `E_(a,b)(m)` for this
element.

*Proof.* Take `(a,p)` with `p <= m`. The factor `λ_ac^m` moves it down to `(a,1)`
in `p-1` steps, then to `(c,1)`, and pushes it to `(c, m-p+1)` in the remaining
`m-p` steps. The factor `λ_cb^m` pulls it up to `(c,1)` in `m-p` steps, then to
`(b,1)`, and pushes it to `(b,p)` in the remaining `p-1` steps. A point `(a,p)` with
`p > m` goes to `(a,p-m)` and is untouched by `λ_cb`. A point `(b,p)` is fixed by
`λ_ac^m` and pushed to `(b,p+m)`. A point `(c,p)` goes to `(c,p+m)` and back to
`(c,p)`. Other rays are fixed. ∎

For `m = 1` this shows that `λ_ac λ_cb λ_bd λ_da = E^c_(a,b)(1) E^d_(a,b)(1)^(-1)`
is trivial.

**Definition.** For `m >= 1` let

```text
W(m) = max { Area( E^c_(a,b)(m) · E^d_(a,b)(m)^(-1) ) : a,b,c,d distinct rays }.
```

This is the cost of changing the route ray of a pour. `W(1) = 1`, by the relator
in `Q`.

**Lemma 1.2 (splitting).** For `m_1, m_2 >= 1`,
`W(m_1 + m_2) <= 2W(m_1) + 2W(m_2) + 4 m_1 m_2 + 2 m_1`.

*Proof.* Fix distinct `a,b,c,d`. Since `n >= 6`, choose rays `e,f` with
`a,b,c,d,e,f` distinct. Put `m = m_1 + m_2`. Free identities give

```text
E^c_(a,b)(m) = λ_ac^(m_1) · E^c_(a,b)(m_2) · λ_cb^(m_1),
λ_ac^(m_1)   ≡ λ_ad^(m_1) · E^a_(d,c)(m_1)        (E^a_(d,c)(m_1) = λ_da^(m_1) λ_ac^(m_1)),
λ_cb^(m_1)   ≡ E^b_(c,d)(m_1) · λ_db^(m_1)        (E^b_(c,d)(m_1) = λ_cb^(m_1) λ_bd^(m_1)).
```

So `E^c_(a,b)(m)` freely equals

```text
λ_ad^(m_1) · E^a_(d,c)(m_1) · E^c_(a,b)(m_2) · E^b_(c,d)(m_1) · λ_db^(m_1).
```

Apply the following moves.

1. Replace `E^a_(d,c)(m_1)` by `E^e_(d,c)(m_1)` and `E^b_(c,d)(m_1)` by
   `E^e_(c,d)(m_1)`. The quadruples `(d,c,a,e)` and `(c,d,b,e)` are distinct, so
   this costs `<= 2W(m_1)`.
2. Replace `E^c_(a,b)(m_2)` by `E^f_(a,b)(m_2)`. This costs `<= W(m_2)`.
3. The word `E^e_(d,c)(m_1)` has `2m_1` letters, all with ray support in
   `{c,d,e}`. The word `E^f_(a,b)(m_2)` has `2m_2` letters, all with ray support
   in `{a,b,f}`. These sets are disjoint. Moving the first word past the second,
   letter past letter, uses `4 m_1 m_2` commutator relators.
4. The word is now
   `λ_ad^(m_1) E^f_(a,b)(m_2) E^e_(d,c)(m_1) E^e_(c,d)(m_1) λ_db^(m_1)`. Here
   `E^e_(d,c)(m_1) E^e_(c,d)(m_1) = λ_de^(m_1) λ_ec^(m_1) λ_ce^(m_1) λ_ed^(m_1)`
   becomes the empty word using `2m_1` relators of the form `λ_xy λ_yx`.
5. Replace `E^f_(a,b)(m_2)` by `E^d_(a,b)(m_2)`. This costs `<= W(m_2)`.

The result is `λ_ad^(m_1) E^d_(a,b)(m_2) λ_db^(m_1)`, which is freely
`E^d_(a,b)(m)`. The total cost is `2W(m_1) + 2W(m_2) + 4m_1m_2 + 2m_1`. ∎

**Proposition 1.3.** There is `K` with `W(m) <= K m^2 (1 + log_2 m)` for all
`m >= 1`.

*Proof.* Let `K = max(3, W(1), W(2)/4, W(3)/9, W(4)/16)`. The bound holds for
`m <= 4` since `1 + log_2 m >= 1`. Let `m >= 5` and put `m_1 = ⌊m/2⌋`,
`m_2 = ⌈m/2⌉`, so `1 <= m_1 <= m_2 < m`. By Lemma 1.2, `4m_1m_2 <= m^2`,
`2m_1 <= m`, and induction,

```text
W(m) <= 2K(m_1^2 + m_2^2)(1 + log_2 m_2) + m^2 + m.
```

Here `m_1^2 + m_2^2 <= (m^2+1)/2`. Also `1 + log_2 m_2 = log_2(2m_2) <= log_2(m+1)`,
and `log_2(m+1) <= log_2 m + 1.45/m`. So

```text
W(m) <= K(m^2+1)(log_2 m + 1.45/m) + m^2 + m
     =  K m^2 log_2 m + K(1.45 m + log_2 m + 1.45/m) + m^2 + m.
```

This is `<= K m^2 (1 + log_2 m)` provided
`K(m^2 - 1.45m - log_2 m - 1.45/m) >= m^2 + m`. For `m >= 5` the bracket is
`>= m^2/2`: at `m = 5` it is `> 15 > 12.5`, and its difference from `m^2/2` is
increasing for `m >= 5`. So it suffices that `K >= 2 + 2/m`, which holds since
`K >= 3`. ∎

## 2. Changing the route of a pushed word

**Lemma 2.1 (route change).** Let `x,u,u'` be distinct rays, `i >= 0`, and `X` a
word all of whose letters have ray support disjoint from `{u,u'}`. Suppose some ray
`e` lies outside `{x,u,u'} ∪ rays(X)`, where `rays(X)` is the union of the ray
supports of the letters of `X`. Then

```text
Area( λ_xu^i X λ_ux^i · (λ_xu'^i X λ_u'x^i)^(-1) ) <= 2W(i) + 2i|X| + 4i.
```

*Proof.* Converting the `2i` formal inverse letters `λ^(-1)` costs `2i`, giving
`λ_xu^i X λ_ux^i λ_xu'^i X^(-1) λ_u'x^i`. Put
`V = λ_ux^i λ_xu'^i = E^x_(u,u')(i)` and `V' = λ_u'x^i λ_xu^i = E^x_(u',u)(i)`.
A cyclic permutation gives `X V X^(-1) V'`.

- If `i = 0` it is freely trivial.
- Otherwise replace `V` by `E^e_(u,u')(i)` and `V'` by `E^e_(u',u)(i)` (the
  quadruples `(u,u',x,e)` and `(u',u,x,e)` are distinct). This costs `<= 2W(i)`.
- The letters of `E^e_(u,u')(i)` have ray support in `{u,u',e}`, which is disjoint
  from `rays(X)`. So `X` passes this word with `2i|X|` relators. The rest is
  `E^e_(u,u')(i) E^e_(u',u)(i) = λ_ue^i λ_eu'^i λ_u'e^i λ_eu^i`, which cancels with
  `2i` relators `λ_xy λ_yx`.

The total is `2W(i) + 2i|X| + 4i`. ∎

For a ray `a`, a ray `b != a` and `k >= 0`, the transposition
`((a,k+1),(a,k+2))` is written, routed via `b`, as

```text
D^b_a(k) = λ_ab^k τ_a λ_ba^k        (length 2k+1, letters in rays {a,b}).
```

Indeed `supp(τ_a)·λ_ba^k` pushes ray `a` out by `k`. By Lemma 2.1 with `X = τ_a`
and `n >= 6`,

```text
R(k) := max_(a,b,c distinct) Area( D^b_a(k) · D^c_a(k)^(-1) ) <= 2W(k) + 6k.       (2.2)
```

## 3. Far commutation

**Theorem 3.1.** Let `n >= 6`. For distinct rays `a,b` and `k >= 0` put

```text
w_k = τ_a · D^b_a(k) · τ_a^(-1) · D^b_a(k)^(-1),
```

which is the commutator of `((a,1),(a,2))` with `((a,k+1),(a,k+2))`. Then
`Area(w_k) <= C k^2 (1 + log_2 k)` for a constant `C` and all `k >= 1`.

For `a = 1, b = 2` the word `w_k` becomes, after the `O(k)` substitutions
`λ_12 = g_1` and `τ_1 = α`, Lee's word `[α, α^(g_1^(-k))]`, up to cyclic conjugation
and inversion. So in Lee's presentation `Area([α, α^(g_1^(-k))]) ≼ k^2 log k` for
every `n >= 6`.

*Proof.* Let `k >= 4`, `m = ⌈k/2⌉` (so `2 <= m <= k`) and `i = k - m`. Choose rays
`c,d` with `a,b,c,d` distinct.

1. *Conjugate.* `h^(-1) w_k h` with `h = λ_ab^m` has the same area. Freely,

   ```text
   λ_ba^m D^b_a(k) λ_ab^m = λ_ab^(k-m) τ_a λ_ba^(k-m) = D^b_a(i),
   λ_ba^m τ_a λ_ab^m.
   ```

2. *Move the top transposition to ray `b`.* Replace `τ_a` by `λ_ab^2 τ_b λ_ba^2`
   (a relator in `Q`), once in each of the two conjugates of `τ_a^(±1)`, at cost 2.
   Now `λ_ba^m τ_a λ_ab^m` is freely `λ_ba^(m-2) τ_b λ_ab^(m-2) = D^a_b(m-2)`.
   The word is freely

   ```text
   D^a_b(m-2) · D^b_a(i) · D^a_b(m-2)^(-1) · D^b_a(i)^(-1).
   ```

3. *Reroute.* Replace both occurrences of `D^a_b(m-2)^(±1)` by `D^c_b(m-2)^(±1)`,
   at cost `2R(m-2)`. Replace both occurrences of `D^b_a(i)^(±1)` by
   `D^d_a(i)^(±1)`, at cost `2R(i)`.
4. *Commute.* The letters of `D^c_b(m-2)` lie in rays `{b,c}` and those of
   `D^d_a(i)` lie in rays `{a,d}`. The commutator of two such words of lengths
   `2m-3` and `2i+1` is killed with `(2m-3)(2i+1)` relators.

The total is `Area(w_k) <= 2 + 2R(m-2) + 2R(i) + (2m-3)(2i+1) + 8k`, where `8k`
bounds the letter conversions `λ_ab^(-1) <-> λ_ba` used by the free identities in
steps 1–2. By (2.2) and
Proposition 1.3, with `m-2, i <= k/2 + 1`, this is `O(k^2 log k)`. The values
`k = 1,2,3` are covered by the constant. ∎

**Remark 3.2 (why this escapes the Tower of Hanoi).** The recorded upper-bound
attempts convert routes inside the rays `{1,2,3}` spanned by the relation itself.
Each conversion then spawns two conversions of comparable size, so
`C(k) <= 2C(k-1) + O(k)`. Here an auxiliary ray `e` makes the pour
`E^e_(u,u')` letterwise disjoint from what it must commute with. Conversions of
size `m` then cost `W(m)`, and `W` halves: `W(2m) <= 4W(m) + 4m^2`. Two auxiliary
rays in Lemma 1.2, on top of the four rays of the pours being compared, force
`n >= 6`.

## 4. The edge graph and edge words

From here on `R(k) <= 2W(k) + 2k ≼ k^2 log k` and `F(k) := max_(a != b) Area(w_k)
≼ k^2 log k` (Theorem 3.1) are used as black boxes.

**The graph `Γ`.** Its vertex set is `Y`. Its edges are

- *ray edges* `t_x(j) = ((x,j),(x,j+1))` for `j >= 1`;
- *top edges* `σ_{x,y} = ((x,1),(y,1))` for `x != y`.

So `Γ` is a complete graph `K_n` on the top vertices `(x,1)`, with a pendant
infinite path hanging from each. Each edge is a transposition, and the *depth* of
an edge is the larger depth of its two vertices. Only top vertices have degree
`>= 3`.

**Edge words.** Fix for each ray `x` a route ray `c(x) != x`. Define

```text
Ed(t_x(j))     = D^(c(x))_x(j-1) = λ_(x c(x))^(j-1) τ_x λ_(c(x) x)^(j-1),   length 2j-1,
Ed(σ_{x,y})    = λ_yx τ_x λ_xy          for x < y.
```

The second word represents `σ_{x,y}`, because `supp(τ_x)·λ_xy = {(y,1),(x,1)}`.
Note `Ed(t_x(1)) = τ_x`. Every word `Ed(e)` has the form `h' τ_x h`, where `h'`
becomes the formal inverse of `h` after letter conversions. So, for an edge of
depth `<= R`,

```text
Area( Ed(e)^2 ) <= 2R + 1          and          Area( Ed(e)^(-1) Ed(e)^(-1) ) <= 2R + 1.       (4.0)
```

For words `U,V` write `[U,V] = U V U^(-1) V^(-1)`. Let `E(R)` be the largest area
of the following *edge relations*, over all edges of depth `<= R`:

- (E1) `Ed(e)^2` for every edge `e`;
- (E2) `[Ed(e), Ed(f)]` for vertex-disjoint edges `e,f`;
- (E3) `Ed(e)Ed(f)Ed(e) · (Ed(f)Ed(e)Ed(f))^(-1)` for edges `e,f` sharing exactly
  one vertex;
- (E4) the *star* and *triangle* relations at top vertices. These are all trivial
  products of at most 13 edge words of the shapes `σ_{x,y}` and `τ_x = t_x(1)`.
  Each such word has length `<= 3`, so the product has length `<= 39`.

**Proposition 4.1.** `E(R) ≼ R^2 log R`.

*Proof.* (E1) costs `<= 2R + 1` by (4.0). (E4) costs 1, since these are relators in
`Q`. Consider (E3).

- If `e,f` are top edges or `t_x(1)`, `t_x(2)`, the relation has length `<= 18`
  and costs `O(1)` (a relator in `Q`, plus the conversions of the formal inverse).
- Otherwise `e = t_x(j)` and `f = t_x(j+1)` with `j >= 2`. Conjugating by
  `λ_(x c(x))^(j-1)` and doing `O(R)` letter conversions, the relation becomes the
  one for `t_x(1)`, `t_x(2)`. So it costs `O(R)`.
- A top edge `σ_{x,y}` and `t_x(j)` share a vertex only if `j = 1`, which is the
  first case.

Consider (E2), with `c = c(x)`.

- *(i) `e = t_x(i)`, `f = t_x(j)`, `j >= i+2`.* Conjugating by
  `λ_(x c)^(i-1)` sends `Ed(e)` freely to `τ_x` and `Ed(f)` to `D^c_x(j-i)`. So
  the relation becomes `w_(j-i)` for the pair `(x,c)`, and the cost is
  `<= F(j-i)`.
- *(ii) `e = t_x(i)`, `f = t_y(j)`, `x != y`.* Choose `c' ∉ {x,y}` and
  `d' ∉ {x,y,c'}`. Reroute both occurrences of `Ed(e)^(±1)` to route `c'`, and both
  occurrences of `Ed(f)^(±1)` to route `d'`, at cost `<= 2R(i-1) + 2R(j-1)`.
  Reroute means: replace `D^(c(x))_x(i-1)` by `D^(c')_x(i-1)` using (2.2), or do
  nothing when `c(x) = c'`. The letters now lie in rays `{x,c'}` and `{y,d'}`, so
  `(2i-1)(2j-1)` commutators finish.
- *(iii) `e = σ_{x,y}`, `f = t_z(j)`, `z ∉ {x,y}`.* Reroute `f` to a route
  `c' ∉ {x,y}` and commute letterwise. The cost is `<= 2R(j-1) + 3(2j-1)`.
- *(iv) `e = σ_{x,y}`, `f = t_x(j)`, `j >= 2`.* First reroute `f` to a route
  `c ∉ {y}` (`<= 2R(j-1)`). The words `λ_yx τ_x λ_xy` and
  `λ_xc λ_yc τ_c λ_cy λ_cx` both represent `σ_{x,y}`. The support of `τ_c` goes
  under `λ_cy` to `{(y,1),(c,1)}`, then under `λ_cx` to `{(y,1),(x,1)}`. So
  replacing the first word by the second costs 1 per occurrence. Applying
  `u -> λ_cx u λ_xc` (area-preserving, plus `O(j)` letter conversions), the
  relation freely becomes `[λ_yc τ_c λ_cy, D^c_x(j-2)]`. Reroute
  `D^c_x(j-2)` to a route `d ∉ {x,y,c}` (`<= 2R(j-2)`). Its letters then lie in
  rays `{x,d}`, and those of `λ_yc τ_c λ_cy` lie in `{y,c}`, so `3(2j-3)`
  commutators finish.
- *(v) Two disjoint top edges.* The relation has length `12`, so it costs 1.

All costs are `≼ R^2 log R`. ∎

**Lemma 4.2 (letters on edges).** Let `s = λ_zw` and let `e` be an edge of depth
`<= R`. Put `e' = s^(-1) e s`, the transposition with support `supp(e)·s`. Then
exactly one of the following holds.

- `e'` is an edge, and `Area( s^(-1) Ed(e) s · Ed(e')^(-1) ) <= 2R̄(R) + 4R + 4`,
  where `R̄(k) = max_(i <= k) R(i)`.
- `e = σ_{w,y}` with `y != z`. Then `e' = ((w,2),(y,1))`, and
  `Area( s^(-1) Ed(e) s · (Ed(t_w(1)) Ed(σ_{w,y}) Ed(t_w(1)))^(-1) ) <= 2`.

*Proof.* `s` sends `(z,p) -> (z,p-1)` for `p >= 2`, `(z,1) -> (w,1)`,
`(w,p) -> (w,p+1)`, and fixes everything else. Go through the edges.

- `t_x(j)` with `x ∉ {z,w}`: `e' = e`. Reroute to `c' ∉ {x,z,w}` (cost `R(j-1)`),
  commute `s` through the `2j-1` letters, cancel `s^(-1)s` freely, and reroute
  back (cost `R(j-1)`).
- `t_z(j)` with `j >= 2`: `e' = t_z(j-1)`. Reroute to route `w`. Then
  `λ_wz · λ_zw^(j-1) τ_z λ_wz^(j-1) · λ_zw = D^w_z(j-2)` freely. Reroute back.
- `t_z(1) = τ_z`: `e' = σ_{z,w}`. The relation has length `<= 6`, so it costs 1.
- `t_w(j)`: `e' = t_w(j+1)`. Reroute to route `z`, which gives freely
  `λ_wz D^z_w(j-1) λ_zw = D^z_w(j)`, then reroute back.
- `σ_{z,w}`: `e' = t_w(1)`. `σ_{z,y}` with `y != w`: `e' = σ_{w,y}`. `σ_{x,y}` with
  `{x,y} ∩ {z,w} = ∅`: `e' = e`. `σ_{w,y}` with `y != z`: the second alternative.
  In each case the relation has length `<= 3 + 2 + 9 <= 40`, so it costs 1, plus 1
  for turning `Ed(σ)^(-1)` into `Ed(σ)` if needed.

Rerouting `D^c_x(i)` costs `<= R(i)`. At most 4 letter conversions occur (for the
formal `s^(-1)` and the adjacent cancellations). ∎

## 5. Path words

From here on, `R̄`, `F̄`, `Ē` are the monotone hulls `max_(i <= k)` of `R`, `F`,
`E`. All three are `≼ k^2 log k`.

**Simple paths in `Γ`.** A *walk word* along a simple path `v_0, v_1, ..., v_r` of
`Γ` with edges `e_k = (v_(k-1) v_k)` is

```text
P(e_1, ..., e_r) = Ed(e_1) ⋯ Ed(e_(r-1)) Ed(e_r) Ed(e_(r-1)) ⋯ Ed(e_1)      (2r-1 edge words).
```

It represents the transposition `(v_0 v_r)`, because `v_r` is fixed by
`e_(r-1), ..., e_1`, and `v_(r-1)·e_(r-1)⋯e_1 = v_0`. Below, a letter `e` inside a
walk word means the edge word `Ed(e)`. Two structural facts are used.

- (S1) In a simple path, `e_i` and `e_k` are vertex-disjoint when `|i-k| >= 2`, and
  share exactly one vertex when `|i-k| = 1`. So (E2) and (E3) apply to them.
- (S2) *Every simple path in `Γ` is a geodesic up to top detours.* Vertices
  `(x,j)` with `j >= 2` have degree 2 and each ray is a pendant path, so a simple
  path never enters a ray other than the rays of its endpoints. So if `v_0, v_r` lie
  on the same ray, the simple path is unique, hence geodesic. If `v_0 = (a,s)` and
  `v_r = (b,t)` with `a != b`, the simple path goes up ray `a` to `(a,1)`, follows a
  simple path `(a,1) = u_0, u_1, ..., u_q = (b,1)` of top vertices, and goes down ray
  `b`. It is the (unique) geodesic iff `q = 1`. In particular a geodesic contains at
  most two top vertices, and they are consecutive on it.

**Canonical words.** Fix a total order on `Y`. For a transposition `ρ = (p q)` with
`p < q`, let `Can(ρ) = P(e_1, ..., e_r)` along the geodesic from `p` to `q`. The
geodesic has `r <= 2R` edges when `p,q` have depth `<= R`.

**Lemma 5.1 (reversal).** For a simple path of `r` edges and depth `<= R`,
`Area( P(e_1,...,e_r) · P(e_r,...,e_1)^(-1) ) <= r^2 Ē(R)`.

*Proof.* Let `T(r)` be the cost, so `T(1) = 0` and `T(2) <= Ē(R)` by (E3). For
`r >= 3`, `P(e_1..e_r) = e_1 P(e_2..e_r) e_1` literally. By induction, replace the
inner block by `P(e_r..e_2) = e_r ⋯ e_3 e_2 e_3 ⋯ e_r`, at cost `T(r-1)`. By (S1),
`e_1` commutes with `e_3, ..., e_r`. Moving both copies of `e_1` inward past them
takes `2(r-2)` applications of (E2) and gives `e_r ⋯ e_3 (e_1 e_2 e_1) e_3 ⋯ e_r`.
One (E3) turns `e_1 e_2 e_1` into `e_2 e_1 e_2`, and the result is `P(e_r..e_1)`.
So `T(r) <= T(r-1) + (2r-3)Ē(R) <= r^2 Ē(R)`. ∎

**Lemma 5.2 (shortcut).** Let `F, σ_(u,w), σ_(w,v), G` be a simple path, where
`F`, `G` are edge sequences and `u,w,v` are distinct top vertices. Then `F, σ_(u,v), G` is a simple
path, and replacing `P(F, σ_(u,w), σ_(w,v), G)` by `P(F, σ_(u,v), G)` costs
`<= (4|G| + 8) Ē(R)`.

*Proof.* Both words have the common prefix `F` and the mirrored suffix. So it is
enough to replace the inner block `σ_uw σ_wv 𝒢 σ_wv σ_uw` by `σ_uv 𝒢 σ_uv`, where
`𝒢 = P(G)` has `2|G|-1` edge words. If `G` is empty, the
block is `σ_uw σ_wv σ_uw`, and one triangle relation (E4) finishes. Otherwise the
edges of `G` avoid `u` and `w` (the first contains `v`, the rest avoid
`u, w, v`), so `σ_uw` commutes with every letter of `𝒢`. Steps:

1. Insert `σ_uw σ_uw` on each side of `𝒢` (two (E1)):
   `σ_uw σ_wv σ_uw · σ_uw 𝒢 σ_uw · σ_uw σ_wv σ_uw`.
2. Move the middle left `σ_uw` through `𝒢` and cancel it with its partner
   (`2|G|-1` (E2) and one (E1)).
3. Replace `σ_uw σ_wv σ_uw` by `σ_uv` twice. These are triangle relations (E4).

The new path is simple, since it uses a subset of the old vertices. ∎

**Corollary 5.3 (normal form).** Let `P(e_1..e_r)` be a walk word along a simple
path of depth `<= R` from `p` to `q`, with `r <= 2R + 4`. Then replacing it by
`Can((p q))` costs `<= C R^2 Ē(R)`.

*Proof.* By (S2) the path is the geodesic with a top detour
`u_0, ..., u_q`, where `q <= n-1`. Apply Lemma 5.2 `q-1 <= n` times, each at cost
`O(R) Ē(R)`. Then, if `p > q` in the fixed order, apply Lemma 5.1. ∎

**Lemma 5.4 (refinement).** Let `v_0..v_r` be a simple path with edges `e_k`, and
let `m` be a vertex not on it such that `f = (v_(k-1) m)` and `g = (m v_k)` are
edges. Replacing the edge word `e_k` in both of its positions in `P(e_1..e_r)` by
`f g f` gives a word `P'`. Then `Area( P' · P(e_1..e_(k-1), f, g, e_(k+1)..e_r)^(-1) )
<= (2r+2) Ē(R)`.

*Proof.* Let `H = e_1 ⋯ e_(k-1)` and `H'` its mirror `e_(k-1) ⋯ e_1`.

- If `k = r`, the edge `e_r` occurs once, and
  `P' = H f g f H' = P(e_1..e_(r-1), f, g)` literally.
- If `k < r`, put `Z = P(e_(k+1)..e_r)`. Then `P' = H f g f Z f g f H'` and the
  target is `H f g Z g f H'`. The edges of `Z` avoid `v_(k-1)` and `m`, so `f`
  commutes with every letter of `Z`. Moving the inner right `f` left through `Z`
  (`<= 2r` (E2)) and cancelling `f f` (one (E1)) turns `f g f Z f g f` into
  `f g Z g f`.

The new path `v_0..v_(k-1), m, v_k..v_r` is simple since `m` is not on the old
path. ∎

**Lemma 5.5 (edge conjugation).** Let `ρ` be a transposition of two points of depth
`<= R`, and `e` an edge of depth `<= R+1`. Then replacing `e Can(ρ) e` by
`Can(ρ^e)` costs `<= C R^2 Ē(R+1)`.

*Proof.* Let `v_0..v_r` be the geodesic of `Can(ρ)`, with edges `e_k`, so
`ρ = (v_0 v_r)`. Write `H = e_1 ⋯ e_(j-1)` and `H'` for its mirror when needed.

- *(C0) `e` is vertex-disjoint from the path.* Then `ρ^e = ρ`. Move the left `e`
  through the `2r-1` letters (E2) and cancel `e e` (E1).
- *(C1) `e = e_k`.*
  - If `r = 1`: `e e e -> e` (one (E1)), and `ρ^e = ρ`.
  - If `k = 1 < r`: `e_1 e_1 P(e_2..e_r) e_1 e_1 -> P(e_2..e_r)` (two (E1)). This
    is a walk word along a simple path from `v_1` to `v_r`, and `ρ^e = (v_1 v_r)`.
    Finish with Corollary 5.3.
  - If `1 < k < r`: `ρ^e = ρ`. Put `Q = P(e_(k+1)..e_r)`, so
    `P = e_1..e_(k-1) e_k Q e_k e_(k-1)..e_1`. By (S1), `e_k` commutes with
    `e_1..e_(k-2)`. Moving the two outer copies of `e_k` inward gives
    `e_1..e_(k-2) (e_k e_(k-1) e_k) Q (e_k e_(k-1) e_k) e_(k-2)..e_1`. Two (E3)
    give `e_(k-1) e_k e_(k-1)` on both sides. Since `e_(k-1)` commutes with `Q`,
    moving the inner `e_(k-1)`s together through `Q` and cancelling them (E2, E1)
    returns `P`. The cost is `O(r) Ē`.
  - If `k = r >= 2`: move both outer `e_r` inward past `e_1..e_(r-2)`, getting the
    block `e_r e_(r-1) e_r e_(r-1) e_r`. By (E3) and (E1) this becomes `e_(r-1)`, so
    the word is `P(e_1..e_(r-1))`, and `ρ^e = (v_0 v_(r-1))`. Use Corollary 5.3.
- *(C2) `e = (v_j y)` with `y` not on the path.*
  - If `j = 0`: `e P e = P(e, e_1..e_r)` literally. This is a simple path from `y`
    to `v_r`, and `ρ^e = (y v_r)`. Use Corollary 5.3.
  - If `j = r`: by Lemma 5.1, `P -> P(e_r..e_1)`. Then `e P(e_r..e_1) e = P(e, e_r..e_1)`,
    a simple path from `y` to `v_0`, and `ρ^e = (v_0 y)`. Use Corollary 5.3.
  - If `0 < j < r`: `ρ^e = ρ`. The vertex `v_j` has degree `>= 3`, so it is a top
    vertex, and `a = e_j`, `b = e_(j+1)`, `e` are edges at a top vertex. Their words
    have length `<= 3`. Put `Q' = P(e_(j+2)..e_r)`, which may be empty. Then
    `P = H a b Q' b a H'`, and `e` commutes with `H` (its edges avoid `v_j` and `y`).
    Moving `e` inward past `H, H'` gives `H (e a b Q' b a e) H'`. Now:
    1. `e a b -> a b (b a e a b)`, since `a b b a e a b` reduces to `e a b` with
       two (E1).
    2. `b a e a b -> a e a` by a star relation (E4). Both sides equal
       `(v_(j-1) y)`.
    3. `a` and `e` avoid the vertices of `Q'`, so `a e a` moves right through `Q'`
       (E2). The word is `H a b Q' (a e a b a e) H'`.
    4. `a e a b a e -> b a` by a star relation (E4): `a e a = (v_(j-1) y) = e^(ab)`,
       so `a e a · b a e = b a`.

    The result is `H a b Q' b a H' = P`.
- *(C3) `e` joins two path vertices but is not a path edge.* This is impossible.
  A ray edge between two geodesic vertices is a path edge. A top edge joins two top
  vertices, and by (S2) the geodesic has at most two, and they are adjacent on it.

Every case uses `O(r)` edge relations plus at most two applications of Lemma 5.1 or
Corollary 5.3. Since `r <= 2R` and all edges have depth `<= R+1`, the cost is
`<= C R^2 Ē(R+1)`. ∎

**Lemma 5.6 (letter conjugation).** Let `ρ` be a transposition of points of depth
`<= R`, and `s ∈ {λ_zw, τ_z}`. Then replacing `s^(-1) Can(ρ) s` by `Can(ρ^s)` costs
`<= C (R R̄(R) + R^2 Ē(R+2))`. Note `supp(ρ^s) = supp(ρ)·s`.

*Proof.* *Case `s = τ_z`.* Convert `τ_z^(-1) -> τ_z` (one relator). Since
`τ_z = Ed(t_z(1))`, Lemma 5.5 with `e = t_z(1)` finishes.

*Case `s = λ_zw`.* Inserting `s s^(-1)` between consecutive edge words is free, so
`s^(-1) Can(ρ) s ≡ ∏ (s^(-1) Ed(e_k) s)` over the `2r-1` edge-word positions of
`P(e_1..e_r)`. Apply Lemma 4.2 at each position, at cost
`<= (2r-1)(2R̄(R) + 4R + 4)`. Let `v_0..v_r` be the geodesic, and `v'_k = v_k·s`.

- *No edge of the path is `σ_(w,y)` with `y != z`.* Then every `e'_k = e_k·s` is an
  edge joining `v'_(k-1)` and `v'_k`. Since `s` is a bijection, `v'_0..v'_r` is a
  simple path, and the word is `P(e'_1..e'_r)`. Corollary 5.3 gives `Can(ρ^s)`.
- *Some `e_k = σ_(w,y)` with `y != z`.* There is only one such edge, since a geodesic
  has at most one top edge. At its positions the word is `t σ t`, where
  `t = Ed(t_w(1))` and `σ = Ed(σ_(w,y))`. Put `m = (w,1)`. Then `m` is not among the
  `v'_i`: `m·s^(-1) = (z,1)`, and the only top vertices of the geodesic are `(w,1)`
  and `(y,1)`, with `z ∉ {w,y}`.
  - If `v_(k-1) = (w,1)` and `v_k = (y,1)`, then `v'_(k-1) = (w,2)` and
    `v'_k = (y,1)`. So `f = t_w(1) = (v'_(k-1) m)` and `g = σ_(w,y) = (m v'_k)`, and
    the block is `f g f`.
  - If `v_(k-1) = (y,1)` and `v_k = (w,1)`, then `f = σ_(w,y)` and `g = t_w(1)`. Turn
    each `t σ t` into `σ t σ = f g f` with one (E3).

  Lemma 5.4 turns the word into the walk word along the simple path
  `v'_0..v'_(k-1), m, v'_k..v'_r`, and Corollary 5.3 gives `Can(ρ^s)`.

All depths involved are `<= R+2`, and `r <= 2R`. ∎

## 6. The Dehn function

**Theorem 6.1.** For every `n >= 6`, the Dehn function of `H_n` satisfies
`δ_(H_n)(x) ≼ x^8 log x`. In particular it is polynomially bounded.

*Proof.* Work in `P`. Put `Γ(R) := C(R R̄(R) + R^2 Ē(R+2)) ≼ R^4 log R`. This
bounds the cost of Lemmas 5.5 and 5.6 at depth `R`, after enlarging `C`. Let `w` be
a null-homotopic word of length `L` in Lee's generators.

1. *Sort.* Lemma 3 of `zp-houghton-dehn-2026-09-13-part1.md` uses only Lee's
   relators and the sorting relations, which are relators of `P`. With `<= C_1 L^2`
   applications it turns `w` into a word freely equal to
   `∏_(k=1)^M d_k^(-1) α^(±1) d_k`, where `M <= C_1 L^2 + L` and
   `|d_k| <= L + C_1`.
2. *Translate.* Convert every letter of every `d_k^(±1)` and every `α^(±1)` into
   letters `λ_xy` and `τ_1`, using the defining relations and letter conversions.
   This takes `O(L)` relators per factor, so `O(L^3)` in total. The factor becomes
   `s_ℓ^(-1) ⋯ s_1^(-1) τ_1 s_1 ⋯ s_ℓ` with `s_i ∈ {λ_xy, τ_x}` and `ℓ <= L + C_1`.
   Here `τ_1 = Ed(t_1(1)) = Can(τ_1)`.
3. *Normalize.* Apply Lemma 5.6 `ℓ` times, from the inside out. The `i`-th step
   replaces `s_i^(-1) Can(ρ_(i-1)) s_i` by `Can(ρ_i)`, where
   `ρ_i = τ_1^(s_1⋯s_i)` has depth `<= i + 2` (Lemma 1 of the 09-13 note). With
   `R := L + C_1 + 2`, this costs `<= ℓ Γ(R)` per factor and `<= M ℓ Γ(R) ≼ L^7 log L`
   in total. The word is now `∏ Can(τ_k)` with `∏ τ_k = 1` in `Sym(B)`, where `B` is
   the set of points of depth `<= R`.
4. *Eliminate.* Run Step 2 of §5 of the 09-13 note, with its `nR` passes of `<= M`
   moves each. Every move there is one of three kinds:
   - a cancellation `Can(ρ) Can(ρ) -> ∅`, which is `2r-1` (E1) from the middle out;
   - an instance of `(ρσρ)`, `Can(ρ) Can(σ) Can(ρ) -> Can(ρσρ)`;
   - an insertion `Can(ρ)Can(ρ)` followed by `(ρσρ)`.

   `Can(ρ)` is the palindrome `e_1 ⋯ e_r ⋯ e_1` in edge words. So `(ρσρ)` follows
   from `2r-1` applications of Lemma 5.5, from the inside out: `e_1 Can(σ) e_1`,
   then `e_2 (·) e_2`, ..., then `e_r`, then `e_(r-1)`, ..., `e_1`. The accumulated
   conjugator is `e_1 ⋯ e_r ⋯ e_1 = ρ`. All intermediate transpositions are
   conjugates of `σ` by edges of depth `<= R`, so they lie in `B`. A move therefore
   costs `<= C R^3 Ē(R+1) + 4R Ē(R) ≼ R^5 log R`.

   Step 4 costs `<= nR · M · C R^5 log R ≼ L^8 log L`.

Adding up, `Area_P(w) ≼ L^2 + L^3 + L^7 log L + L^8 log L`. By §0,
`Area_Lee(w) <= K Area_P(w)`. ∎

**Remark 6.2 (what the theorem does and does not settle).**

- For `n >= 6` it answers the first question of Zaremsky Problem 1.24
  (polynomiality). Quadraticity stays open, and the exponent 8 is not optimized.
- The argument never uses the commutation area `A(ℓ)` directly. It bypasses the
  circular transport of the 09-13 note: all route conversions go through pours with
  two auxiliary rays (Lemma 1.2), which halve.
- For `n ∈ {3,4,5}`, Lemma 1.2 has no two free auxiliary rays, and the question
  stays open. The hypothesis `n >= 6` enters only through Lemma 1.2, and hence
  through `W`. Every other step chooses at most four distinct rays at a time.
