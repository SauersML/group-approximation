---
rg: 2
id: tail-uniform-germ-extensions-of-v-are-not-fp-proof
kind: route
title: Marked relations of tail-uniform extensions of V depend on finitely many bits of the tail, and flipping one deep bit breaks a relation that a finite presentation would force
target: tail-uniform-germ-extensions-of-v-are-not-fp
requires: []
---

Notation is that of the target node. Throughout, `x` is not eventually
periodic. All templates are admissible at `x`. *Letter* means a template map or
the inverse of one, and letters include the elements of a fixed finite
generating set `S_V` of `V`. Write `g_y` for `g_(τ,y)`.

For a point `b` and `m >= 0`, the **ring of depth `m` around `b`** is
`R_m(b) = C(b|m ¬b_(m+1))`. Every `p ≠ b` lies in exactly one ring, and its
depth is its *relative depth* from `b`.

## Lemma A (template maps)

**A1. Well defined, and the inverse is a template.** If `τ` is admissible at
`y`, then `g_y` is a homeomorphism of `C`.
- Each prefix pair is a homeomorphism `C(u_i) -> C(u'_i)`.
- On `W_k(y)` the relative shift is a bijection onto `W'_k(y)`: ring depth
  `n >= n_k` from `z_k(y)` goes to ring depth `n + δ_k >= n_k + δ_k` from
  `z'_k(y)`, and each ring map is a prefix replacement.
- It is continuous at `z_k(y)`, since deep rings go to deep rings.
- The pieces partition source and target.

Its inverse is `g_(τ*,y)`. The template `τ*` has the reversed prefix pairs and
the data `(a'_k, j'_k, n_k + δ_k ; a_k, j_k, -δ_k)`, with offset `-o_k`. So
inverses of letters are letters of the same kind.

**A2. Admissibility is local in `y`.** The words defining the pieces use only
bits of `y` up to `L_τ = max_k (j_k + n_k, j'_k + n_k + δ_k)`. So admissibility
at `y`, and the list of pieces as words, depend only on `y|L_τ`. Fix `N_0` at
least every `L_τ` involved. For `y|N_0 = x|N_0` every template is admissible at
`y` with the same prefix pairs.

**A3. Local form away from singular points.** Let `p_0 ≠ z_k(x)` for all `k`.
There are a prefix pair `P -> P'`, with `P` a prefix of `p_0`, and an `N` such
that for every `y` with `y|N = x|N`:
- `C(P)` is contained in a piece of `g_y`;
- `g_y` acts on `C(P)` as `Pq -> P'q`.

*Proof.* There are two cases.
- If `p_0 ∈ C(u_i)`, take `P = u_i` and `P' = u'_i`.
- Otherwise `p_0 ∈ W_k(x) \ {z_k(x)}` for some `k`, at some depth `n >= n_k`.
  Take `P = a_k x_(j_k+1..j_k+n) ¬x_(j_k+n+1)` and
  `P' = a'_k x_(j'_k+1..j'_k+n+δ_k) ¬x_(j'_k+n+δ_k+1)`. These words use bits of
  `x` only up to `J = max(j_k + n, j'_k + n + δ_k) + 1`. For
  `y|max(N_0, J) = x|max(N_0, J)` they are the same words built from `y`, so
  `C(P)` is the depth-`n` ring of `W_k(y)` and `g_y` maps it by `P -> P'`. ∎

**A4. Relative form of a prefix replacement.** Suppose `g` acts on `C(P)` as
`P -> P'`, and `b ∈ C(P)`. Then for every `m >= |P|`,

    g( R_m(b) ) = R_(m + |P'| - |P|)( g(b) ),

and the tail `q` after the ring prefix is kept.

*Proof.* `p = b|m ¬b_(m+1) q` lies in `C(P)`. Also
`g(p) = P' b_(|P|+1..m) ¬b_(m+1) q`, and `g(b) = P' b_(|P|+1..)`. ∎

**A5. Relative form at a singular point.** For `y|N_0 = x|N_0`, every `k` and
every `m >= |a_k| + n_k`,

    g_y( R_m(z_k(y)) ) = R_(m + Δ_k)( z'_k(y) ),   Δ_k = |a'_k| - |a_k| + δ_k,

and the tail `q` is kept.

*Proof.* `R_m(z_k(y))` is the depth-`(m - |a_k|)` ring of `W_k(y)`. Apply the
definition. ∎

## Representations

A *representation* is a pair `r = (a, j)` of a word and an integer `j >= 0`. Its
value at `y` is `ev_y(r) = a σ^j y`. Two facts will be used.
- **Bit locality.** Bit `t` of `ev_y(a,j)` is a bit of `a` or equals
  `y_(t - |a| + j)`. So `ev_y(r)|T = ev_x(r)|T` whenever
  `y|(T + j) = x|(T + j)`.
- **Continuity in `y`.** It follows that `ev_y(r) -> ev_x(r)` as `y -> x`.

**Lemma B0 (equality is decided by finite data).** Let `r = (a,j)` and
`r' = (a',j')`. There is `N` such that for every `y` with `y|N = x|N`,

    ev_y(r) = ev_y(r')   if and only if   ev_x(r) = ev_x(r').

*Proof.* Put `J = max(j, j')`, `b = a x_(j+1..J)` and `b' = a' x_(j'+1..J)`.
Then `ev_x(r) = b σ^J x` and `ev_x(r') = b' σ^J x`. The same holds with `y` in
place of `x` whenever `y|J = x|J`.
- *Equal words.* If `b = b'`, both sides are equal for every such `y`.
- *Unequal words of equal length.* If `|b| = |b'|` and `b ≠ b'`, the values
  differ in a bit of `b` for every such `y`.
- *Unequal lengths.* If `|b| < |b'|`, write `b' = b_0 c` with `|b_0| = |b|`.
  - If `b_0 ≠ b`, the values differ for every such `y`.
  - If `b_0 = b` and `ev_x(r) = ev_x(r')`, then `σ^J x = c σ^J x` with `c`
    nonempty. So `σ^J x` is periodic and `x` is eventually periodic, which is
    excluded. Hence `ev_x(r) ≠ ev_x(r')`. Let them differ at bit `t`. By bit
    locality they still differ at bit `t` when `y|(t + J) = x|(t + J)`.

Take `N` to be the largest bound used. ∎

**Lemma B (mirroring).** Let `ℓ_1, ..., ℓ_L` be letters and `r_0` a
representation. There are representations `r_1, ..., r_L` and `N` such that for
every `y` with `y|N = x|N` and every `t = 1..L`:
1. `ev_y(r_t) = ℓ_(t,y)( ev_y(r_(t-1)) )`;
2. `ev_y(r_(t-1))` is a singular point `z_k(y)` of `ℓ_t` exactly when
   `ev_x(r_(t-1)) = z_k(x)`;
3. if `ev_x(r_(t-1))` is not singular for `ℓ_t`, there is a prefix pair
   `P_t -> P'_t` for which `ℓ_(t,y)` acts on `C(P_t)` as `P_t -> P'_t`, and
   `ev_y(r_(t-1)) ∈ C(P_t)`.

*Proof.* Induction on `t`. Let `r_(t-1) = (a, j)` and `z = ev_x(r_(t-1))`.
Condition 2 holds for `y` near `x` by Lemma B0, applied to `r_(t-1)` and each
`(a_k, j_k)`.

- **Case `z = z_k(x)`.** For `y` near `x` we have `ev_y(r_(t-1)) = z_k(y)`, and
  `ℓ_(t,y)` sends it to `z'_k(y)`. Put `r_t = (a'_k, j'_k)`.
- **Case `z` not singular.** Take `P = P_t` and `P' = P'_t` from A3 at
  `p_0 = z`. By bit locality, `ev_y(r_(t-1)) ∈ C(P)` for `y` near `x`. Define
  `r_t` as follows:
  - `r_t = (P' a_(|P|+1..|a|), j)` when `|P| <= |a|`;
  - `r_t = (P', j + |P| - |a|)` otherwise.

  In both cases `ev_y(r_t) = P' σ^|P| ( ev_y(r_(t-1)) ) = ℓ_(t,y)(ev_y(r_(t-1)))`.

`N` is the maximum of the finitely many bounds used. ∎

## Lemma C (locality of relations in the tail)

Let `w = ℓ_L ⋯ ℓ_1` be a word in letters, and suppose `w_x = id`. Then there is
`N` such that `w_y = id` for every `y` with `y|N = x|N`.

*Proof.* Suppose not. Then there are points `y^(s) -> x` and points `p^(s)`
with `w_(y^(s))(p^(s)) ≠ p^(s)`. By compactness, pass to a subsequence with
`p^(s) -> p*`. Put `p*_0 = p*` and `p*_t = ℓ_(t,x)(p*_(t-1))`. Then
`p*_L = p*`, since `w_x = id`.

**Case 1. No `p*_(t-1)` is a singular point of `ℓ_t`.**
- *Local form at each step.* By A3, for each `t` there are a cylinder
  `C(P_t) ∋ p*_(t-1)` and a bound `N_t`. For every `y` with
  `y|N_t = x|N_t`, `ℓ_(t,y) = ℓ_(t,x)` on `C(P_t)`.
- *Nested neighbourhoods.* Define open sets `Q_t` backwards: `Q_(L+1) = C` and
  `Q_t = C(P_t) ∩ ℓ_(t,x)^-1(Q_(t+1))`. Then `p*_(t-1) ∈ Q_t`.
- *Conclusion.* Put `N = max N_t`. For `y|N = x|N` and `p ∈ Q_1`, induction on
  `t` shows that the `t`-th images of `p` under `y` and under `x` coincide. So
  `w_y(p) = w_x(p) = p`.

Eventually `(y^(s), p^(s))` satisfies `y^(s)|N = x|N` and `p^(s) ∈ Q_1`. That
is a contradiction.

**Case 2. Some `p*_(t_0-1)` equals a singular point `z_k(x)` of `ℓ_(t_0)`.**

*Setup.* Apply Lemma B to the cyclically rotated letter sequence
`ℓ_(t_0), ..., ℓ_L, ℓ_1, ..., ℓ_(t_0-1)`, starting from `r_(t_0-1) = (a_k, j_k)`.
It gives representations `r_t` for `t = t_0, ..., L`, then `r_1, ..., r_(t_0-2)`,
and a final `r_end`.
- Write `r_0` for the one produced at position `L`.
- For `y` near `x` put `b_t(y) = ev_y(r_t)`. These values also exist at `y = x`
  and there follow `p*`, so `b_t(x) = p*_t`.
- The rotated word fixes `z_k(x)`, since it is a cyclic conjugate of
  `w_x = id`. So `ev_x(r_end) = ev_x(r_(t_0-1))`, and Lemma B0 gives
  `ev_y(r_end) = ev_y(r_(t_0-1))` for `y` near `x`.
- Following the letters `ℓ_1, ..., ℓ_L` from `b_0(y)` therefore returns to
  `b_0(y)`:

      w_y( b_0(y) ) = b_0(y).                                      (C.1)

*Step shifts.* Each step moves rings by a fixed amount. For `y` near `x`, each
`t` has constants `m_t` and `Δ_t` with

    ℓ_(t,y)( R_m(b_(t-1)(y)) ) = R_(m+Δ_t)( b_t(y) )   for all m >= m_t,   (C.2)

and the tail after the ring prefix is kept.
- If `p*_(t-1)` is singular for `ℓ_t`, use A5: `m_t = |a| + n` and
  `Δ_t = |a'| - |a| + δ` for the datum `(a, j, n ; a', j', δ)` in question.
- Otherwise use A4 with the pair `P_t -> P'_t` of Lemma B(3):
  `m_t = |P_t|` and `Δ_t = |P'_t| - |P_t|`.

*Relative form of `w`.* Put `Δ = Σ Δ_t` and `m* = max_t m_t + Σ_t |Δ_t|`.
Composing (C.2) and using (C.1), for `y` near `x` and `m >= m*`,

    w_y( b_0(y)|m ¬b_0(y)_(m+1) q ) = b_0(y)|(m+Δ) ¬b_0(y)_(m+Δ+1) q.    (C.3)

*`Δ = 0`.* At `y = x` the left side of (C.3) is the point itself, since
`w_x = id`, and `b_0(x) = p*`.
- If `Δ > 0`, the right side agrees with `p*` at bit `m+1` and the left side
  does not.
- If `Δ < 0`, the right side differs from `p*` at bit `m+Δ+1 <= m` and the left
  side agrees with `p*` there.

So `Δ = 0`. By (C.1) and (C.3), `w_y` fixes every point of `C(b_0(y)|m*)` for
all `y` near `x`.

*Contradiction.* By continuity in `y`, `b_0(y^(s)) -> p*`, and `p^(s) -> p*`.
So eventually `p^(s) ∈ C(p*|m*) = C(b_0(y^(s))|m*)`, and `p^(s)` is fixed by
`w_(y^(s))`. This is a contradiction. ∎

Only the non-eventual periodicity of `x` is used, through Lemma B0. The
neighbour `y` may be eventually periodic.

## Lemma D (offset zero is exactly a V-germ)

Let `(a, j, n_0 ; a', j', δ)` be a singular datum of `τ`, with offset
`o = j' + δ - j`.

**If `o = 0`, then `g_x` is a prefix replacement on `W(x)`.**
- If `δ <= 0`, then `j' >= j`, and on `W(x)` the map `g_x` is the replacement
  `a x_(j+1..j') -> a'`. This is defined because `n >= n_0 >= 1 - δ > j' - j`.
- If `δ > 0`, the replacement is `a -> a' x_(j'+1..j)`.

Check this by writing out both sides of the relative shift with `j' = j - δ`.

**If `o ≠ 0`, the germ of `g_x` at `z = a σ^j x` is not a V-germ.** Suppose
instead that `g_x` acts near `z` by a replacement `P -> P'`, with `P` a prefix
of `z`.
- *The tail bit.* For large `n`, compare the two expressions for the image of
  `a x_(j+1..j+n) ¬x_(j+n+1) q`. Each has the form `(finite word) q`. Equal
  total lengths give `|P'| - |P| = |a'| - |a| + δ`.
- *The last bit before `q`.* It is `¬x_(j+n+1)` in the replacement expression
  and `¬x_(j'+n+δ+1)` in the relative shift. So `x_(i) = x_(i+o)` for all large
  `i`, and `x` is eventually periodic. This is a contradiction.

**Consequence.** Suppose every datum of `τ` has offset `0`. By the first part
`g_x` is locally a prefix replacement at every point. By compactness, finitely
many cylinders cover `C`, and on each of them `g_x` is a prefix replacement.
Refining to a common partition gives a partition of `C` into cylinders, and the
images of those cylinders are again cylinders that partition `C`. So `g_x ∈ V`.

## Proof of the theorem

For any `y` with `y|N_0 = x|N_0`, let `G_y` be the marked group generated by
`S_V` together with `g_(τ_1,y), ..., g_(τ_m,y)`. Then `G = G_x`.

**Step 1. A finite presentation certifies nearby parameters.** Suppose `G` is
finitely presented. Finite presentability does not depend on the finite
generating set (Tietze), so `G = <S | R>` with `R` finite, on the letters
`S = S_V ∪ {g_(τ_i)}`. Each `r ∈ R` satisfies `r_x = id`. Lemma C gives `N_r`
with `r_y = id` whenever `y|N_r = x|N_r`. Put `N = max(N_0, max_r N_r)`.

For every `y` with `y|N = x|N`, the assignment `s -> s` on `S_V` and
`g_(τ_i,x) -> g_(τ_i,y)` kills `R`. So it extends to an epimorphism
`π_y : G -> G_y`, and

    every word that is trivial in G_x is trivial in G_y.                  (*)

**Step 2. One flipped bit breaks a relation.** Let `(a, j, n_0 ; a', j', δ)` be
a datum of `τ = τ_i` with offset `o = j' + δ - j ≠ 0`, and write `g = g_(τ_i)`.
Fix `M >= max(N, n_0)`. Let `y` agree with `x` except at bit `j + M + 1`. Then
`y|N = x|N`. Since `o ≠ 0`, the position `j' + M + δ + 1` differs from
`j + M + 1`, so

    y_(j'+M+δ+1) = x_(j'+M+δ+1).                                         (1)

Put
- `P = a x_(j+1..j+M) ¬x_(j+M+1)`, which equals `a y_(j+1..j+M+1)`;
- `P' = a' x_(j'+1..j'+M+δ) ¬x_(j'+M+δ+1)`.

Here `M + δ >= n_0 + δ - 1 >= 0`.

*At `x`.* `C(P)` is the depth-`M` ring of `W(x)`, since `M >= n_0`. So `g_x` maps
`C(P)` onto `C(P')` by `P -> P'`.

*At `y`.* `C(P) = C(a (σ^j y)|(M+1)) ⊆ W(y)` contains `z(y)` and the rings of
depth `>= M+1`. By the relative shift,

    g_y(C(P)) ⊆ C( a' y_(j'+1..j'+M+δ+1) ).

By (1) the bit at position `|a'| + M + δ + 1` of this cylinder is
`x_(j'+M+δ+1)`. The same bit of `C(P')` is `¬x_(j'+M+δ+1)`. So

    g_y(C(P)) ∩ C(P') = ∅.                                              (2)

*The relation.* Let `f ∈ V` swap `C(P0)` and `C(P1)`, and let `f' ∈ V` swap
`C(P'0)` and `C(P'1)`. Fix words for `f` and `f'` in `S_V`.
- In `G_x` we have `g_x f g_x^-1 = f'`. Indeed `g_x` is the replacement
  `P -> P'` from `C(P)` onto `C(P')`, and `f` is supported in `C(P)`.
- In `G_y` the element `g_y f g_y^-1` is nontrivial and supported in
  `g_y(C(P))`. The element `f'` is nontrivial and supported in `C(P')`. By (2)
  these supports are disjoint, so `g_y f g_y^-1 ≠ f'`.

So the word `g f g^-1 f'^-1` is trivial in `G_x` and not in `G_y`, which
contradicts (*). Hence `G` is not finitely presented. ∎

## Proof of the corollary

- **`x` not eventually periodic.** The theorem forces every offset to be `0`.
  Lemma D then puts every `g_(τ_i,x)` in `V`, so `G = V`, which is rational.
- **`x` eventually periodic.** Use the standard criterion that a homeomorphism
  of `C` is rational iff it has finitely many restrictions (Grigorchuk,
  Nekrashevych and Sushchanskii, *Automata, dynamical systems and groups*,
  2000, §2). The restriction `g|_w` is the map `q -> g(wq)` with the longest
  common prefix of `g(C(w))` deleted. Consider the restrictions of
  `g = g_(τ,x)` at a word `w`.
  - At words shorter than the pieces there are finitely many.
  - Inside `C(u_i)`, or inside a ring of some `W_k(x)`, the restriction is the
    identity once `w` reaches past the piece or ring prefix.
  - At `w = a_k x_(j_k+1..j_k+n)` with `n >= n_k`, the restriction is the
    relative shift from the point `σ^(j_k+n) x` to `σ^(j'_k+n+δ_k) x`, with
    depth shift `0`. It is determined by this pair of points, and the pair takes
    finitely many values because `x` is eventually periodic.

  So `g` is rational. The group `V` is rational, so `G` consists of rational
  homeomorphisms. By `rational-homeomorphism-subgroups-have-exponential-wp`
  its word problem is in `2^O(n)`. ∎

## Main example check

`h_x` agrees with `g_(τ,y)` at `y = x`, for the template
`τ = { ¬x_1 -> ¬x_1 0 , x_1¬x_2 -> ¬x_1 1 ; (ε, 0, 2 ; ε, 0, -1) }`.
- `W(y) = C(y|2)`, and its depth-`n` ring `A_n^y` goes to `A_(n-1)^y` for
  `n >= 2`.
- The domains `C(¬x_1)`, `C(x_1¬x_2)`, `C(x_1x_2)` partition `C`.
- The images `C(¬x_1 0)`, `C(¬x_1 1)`, `C(x_1)` partition `C`.
- The offset is `0 + (-1) - 0 = -1`.

Step 2 at `(a, j) = (ε, 0)` is exactly the word-problem test of the target node:
the relation `h f h^-1 = f'` with `P = x|M ¬x_(M+1)`, broken by flipping
`x_(M+1)`.
