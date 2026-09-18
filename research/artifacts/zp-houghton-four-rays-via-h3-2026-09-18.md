# Houghton H_4 reduces to H_3: the four-ray skew square factors through two ray-fixing copies of H_3

Lane swarm-0917-w9-w9-z-follow, 2026-09-18. Zaremsky Problem 1.24. Status: complete
proof of a reduction, unreviewed. The combinatorial identity it uses is machine-checked
(§4).

Notation, the presentation `P` (for `n = 4`) and `W(m)` are as in
`research/artifacts/zp-houghton-pours-2026-09-17.md` (the "six-ray note"), §0–§1:
points `(x,p)`, `p >= 1`; right actions, words read left to right; `λ_xy` pulls ray
`x` in and pushes ray `y` out; `τ_x = ((x,1),(x,2))`;
`E^c_(a,b)(m) = λ_ac^m λ_cb^m`; and

```text
W(m) = max { Area_P( E^c_(a,b)(m) · E^d_(a,b)(m)^(-1) ) : a,b,c,d distinct rays }.
```

For `n = 4` the word `E^c_(a,b)(m) E^d_(a,b)(m)^(-1)` is, after `2m` letter conversions,
the four-ray skew square `λ_ac^m λ_cb^m λ_bd^m λ_da^m` of
`research/artifacts/zp-houghton-five-rays-2026-09-17.md` §5.

## 0. The point

The w8 note (five-ray artifact §5) says a four-ray bound on `W` "needs a genuinely
two-dimensional filling of the skew square", because every route of one pour moves a ray
of the other, so no letterwise commutation is available. That is true inside the pour
calculus. But the skew square does not need a new two-dimensional trick in `H_4`: it is
the boundary of two discs, each of which lives in a copy of `H_3`.

- The element `E_(a,b)(m)` is supported on rays `a,b`, so it lies in the subgroup
  `S_c ∩ S_d`, where `S_x` is the pointwise stabilizer of ray `x`.
- `S_d ≅ H_3` (rays `a,b,c`) and `S_c ≅ H_3` (rays `a,b,d`).
- `E_(a,b)(m)` has a word `N_(a,b)(m)` of length `<= m^3` in the letters
  `λ_ab, λ_ba, τ_b`, which lie in both `S_c` and `S_d`.

So the skew square is the product of the two null-homotopic words
`E^c N^(-1)` (in `S_d`) and `N E^(d)(-1)` (in `S_c`), each of length `<= 2m^3`. Each is
filled inside its copy of `H_3`. Hence `W_4(m) ≼ δ_(H_3)(m^3)`, and a polynomial Dehn
function for `H_3` gives one for `H_4`.

## 1. The two-ray normal form of a pour

For distinct rays `a,b` and `j >= 1` put

```text
s_j = λ_ba^(j-1) τ_b λ_ab^(j-1)        (= D^a_b(j-1) of the six-ray note, §2),
```

the transposition `((b,j),(b,j+1))`: the support `{(b,1),(b,2)}` of `τ_b` is pushed out
`j-1` steps by `λ_ab^(j-1)`. Define

```text
ρ_b(m)     = Π_(i = m-1, ..., 1) ( s_1 s_2 ⋯ s_i ),
N_(a,b)(m) = λ_ab^m · ρ_b(m).
```

**Lemma 1.** As elements of `H_n` (any `n >= 3`, any ray `c ∉ {a,b}`),
`E^c_(a,b)(m) = N_(a,b)(m)`. The word `N_(a,b)(m)` uses only the letters `λ_ab`,
`λ_ba`, `τ_b`, and `|N_(a,b)(m)| = m + Σ_(i<m) i^2 <= m^3`.

*Proof.* By Lemma 1.1 of the six-ray note, `E_(a,b)(m)` sends `(a,p) -> (b,p)` for
`p <= m`, `(a,p) -> (a,p-m)` for `p > m`, `(b,p) -> (b,p+m)`, and fixes the rest. The
word `λ_ab^m` sends `(a,p) -> (b, m+1-p)` for `p <= m`: the point walks up to `(a,1)`
in `p-1` steps, jumps to `(b,1)`, and is pushed out `m-p` more steps. It agrees with
`E_(a,b)(m)` on all other points. So `E_(a,b)(m) = λ_ab^m · r`, where `r` is the
reversal `(b,q) <-> (b,m+1-q)` of the first `m` points of ray `b` (right action: first
`λ_ab^m`, then `r`). The word `Π_(i=m-1..1) (s_1 ⋯ s_i)` is the bubble-sort word of the
longest element of `Sym(m)` in the adjacent transpositions `s_j = ((b,j),(b,j+1))`, so
it represents `r`. Lengths: `|s_j| = 2j-1` and
`Σ_(i=1)^(m-1) Σ_(j=1)^i (2j-1) = Σ_(i<m) i^2`. ∎

So `|E^c_(a,b)(m) · N_(a,b)(m)^(-1)| <= 2m + m^3 <= 2m^3` for `m >= 2`.

## 2. Area transfer from a ray stabilizer

For a ray `x` of `H_4` let `S_x = { g ∈ H_4 : g fixes ray x pointwise }`. Restriction
to the other three rays is an isomorphism `S_x ≅ H_3`. An element of `S_x` is a
permutation of the three remaining rays that is eventually a translation on each of
them. Conversely, every such permutation extends by the identity on ray `x`. A letter
`λ_yz` of `P` lies in `S_x` iff `x ∉ {y,z}`, and `τ_y` lies in `S_x` iff `x != y`.

**Lemma 2.** There are constants `K, C`, depending only on the presentations, such that
every null-homotopic word `w` of `P` all of whose letters lie in `S_x` satisfies

```text
Area_P(w) <= K ( |w| + δ_(H_3)(C|w|) ).
```

*Proof.* Fix a finite presentation `<X | R>` of `H_3`, for instance Lee's (Theorem C of
arXiv:1212.0257, quoted verbatim in `houghton-groups-have-at-most-exponential-dehn-function`),
and fix the isomorphism `S_x ≅ H_3`. For each of the finitely many letters `ℓ` of `P`
that lie in `S_x`, choose an `X`-word `θ(ℓ)` representing it. For each `y ∈ X`, choose
a `P`-word `ι(y)` representing the corresponding element of `S_x ⊂ H_4`. Let
`C = max |θ(ℓ)|`.

1. `θ(w)` is a null-homotopic `X`-word of length `<= C|w|`. So it has a van Kampen
   diagram over `R` with at most `δ_(H_3)(C|w|)` cells.
2. Apply `ι` to that diagram. Each relator `r ∈ R` becomes the null-homotopic `P`-word
   `ι(r)`, of bounded length. Let `K_1 = max_(r ∈ R) Area_P(ι(r))`, which is finite
   because `R` is finite. So `Area_P(ι(θ(w))) <= K_1 δ_(H_3)(C|w|)`.
3. For each letter `ℓ`, the word `ℓ^(-1) ι(θ(ℓ))` is null-homotopic in `H_4`. Let
   `K_2` be the largest of their (finitely many) `P`-areas. Replacing the letters of
   `w` one at a time by `ι(θ(ℓ))` costs `<= K_2 |w|`.

With `K = max(K_1, K_2)` the bound follows. ∎

This is the standard fact that, on words in a finitely presented subgroup, the ambient
area is at most a constant times the subgroup's Dehn function. Nothing about Houghton
groups is used except `S_x ≅ H_3`.

## 3. The reduction

**Theorem 3 (four-ray route changes are bounded by the H_3 Dehn function).** For
`n = 4` there are constants `K, C` with

```text
W(m) <= 2K ( 2m^3 + δ_(H_3)(2C m^3) )          for all m >= 2.
```

In particular, if `δ_(H_3)(x) ≼ x^d`, then `W(m) ≼ m^(3d)` for `n = 4`.

*Proof.* Fix distinct rays `a,b,c,d` of `H_4`. Put `N = N_(a,b)(m)`. The word
`E^c_(a,b)(m) E^d_(a,b)(m)^(-1)` is freely equal to

```text
( E^c_(a,b)(m) · N^(-1) ) · ( N · E^d_(a,b)(m)^(-1) ).
```

Both factors are null-homotopic by Lemma 1. The letters of the first are `λ_ac`,
`λ_cb` and the letters of `N`, which are `λ_ab`, `λ_ba`, `τ_b`. None has `d` in its ray
support, so all lie in `S_d`. The letters of the second are `λ_ad`, `λ_db` and those of
`N`, all in `S_c`. Each factor has length `<= 2m^3`. Lemma 2, applied with `x = d` and
with `x = c`, bounds each area by `K(2m^3 + δ_(H_3)(2Cm^3))`. Areas add under products
of null-homotopic words. ∎

**Theorem 4 (H_3 polynomial implies H_4 polynomial).** If `δ_(H_3)(x) ≼ x^d`, then
`δ_(H_4)(x) ≼ x^(6+3d)`.

*Proof.* Run Theorem C of `research/artifacts/zp-houghton-five-rays-2026-09-17.md` with
`n = 4` and `β = 3d`, using Theorem 3 in place of Proposition B. Theorem C uses `n >= 5`
only through `W`: its ray check shows that every step other than the bound on `W` needs
at most four distinct rays. I re-checked the ray choices in the six-ray note for
`n = 4`:

- Lemma 2.1 uses `x,u,u',e`, with `X = τ_x`.
- Theorem 3.1 uses `a,b,c,d`.
- Proposition 4.1 (ii) uses `c' ∉ {x,y}` and `d' ∉ {x,y,c'}`. Case (iii) uses a route
  `c' ∉ {x,y}` for a ray `z ∉ {x,y}`. Case (iv) uses `c ∉ {x,y}` and `d ∉ {x,y,c}`.
- Lemma 4.2 reroutes `t_x(j)`, `x ∉ {z,w}`, to `c' ∉ {x,z,w}`.
- §5 and §6 choose no new rays.

Each uses at most four rays. The exponent bookkeeping of Theorem C assumes only
`W ≼ m^β` with `β >= 2` (all extra terms are `O(R^2)`), and `β = 3d >= 6`. It gives
`Area ≼ L^(6+β)`. ∎

So the route split of `houghton-groups-have-polynomial-dehn-function` by ray count has
effectively one hole, `H_3`: polynomial Dehn functions for all Houghton groups are
equivalent to a polynomial Dehn function for `H_3` alone.

**Remark 3.1 (a sharper need).** The proof of Theorem 3 uses `δ_(H_3)` only on one
explicit family. Put

```text
A_3(m) = Area_(H_3)( E^c_(a,b)(m) · N_(a,b)(m)^(-1) )      (rays a,b,c of H_3).
```

Then `W_4(m) <= 2K(2m^3 + A_3(m))` with the same argument, where Lemma 2 is applied to
one fixed word instead of via `δ_(H_3)`. So `A_3(m) ≼ m^D` already gives
`δ_(H_4) ≼ x^(6+D)`. `A_3` says: the three-ray pour `λ_ac^m λ_cb^m` can be rewritten
into the two-ray word `λ_ab^m ρ_b(m)` with polynomial area.

## 4. Machine check

`experiments/houghton-four-rays-2026-09-17/verify_two_ray_factorization.py` checks
Lemma 1 and the letter bookkeeping of Theorem 3 for all 24 labelings `(a,b,c,d)` of the
four rays and `1 <= m <= 7`:

- `E^c_(a,b)(m)`, `E^d_(a,b)(m)` and `N_(a,b)(m)` are equal as elements. They are
  compared on every point of depth `<= max length + 2`. Deeper points move by the common
  translation vector.
- `E^c N^(-1)` has no letter touching ray `d`, and `N E^d(-1)` has no letter touching
  ray `c`. Every letter of `N` has ray support in `{a,b}`.
- `|N| = m + Σ_(i<m) i^2 <= m^3` and `|E^c| + |N| <= 2m^3` for `m >= 2`.

Output:

```text
checked 168 cases (24 labelings, 1 <= m <= 7): E^c = E^d = lam_ab^m rho_b(m) as elements; rho_b(m) uses only lam_ab, lam_ba, tau_b; |N| <= m^3
```

## 5. What this changes, and what is left

- **Belief changed.** The w8 note records `H_4` as an independent hole "where a
  genuinely two-dimensional filling of the skew square" is needed. It is not
  independent: every four-ray skew square is the boundary of two `H_3`-discs glued
  along a two-ray word. So the four-ray difficulty is at most the three-ray one.
- **The program's single hole.** `houghton-groups-have-polynomial-dehn-function` now
  follows from `houghton-group-h3-has-polynomial-dehn-function` alone, through the
  ray-count route (`n >= 5` proved, `n = 4` by Theorem 4).
- **Why this does not go down to `H_3`.** The two-ray subgroups
  `S_c ∩ S_d ≅ FSym ⋊ Z` are not finitely presented (`houghton-h2-is-not-fp2-over-q`).
  So there is no smaller finitely presented piece to fill in, and the gluing trick
  stops at three rays. A counterexample to polynomiality, if there is one, lives in
  `H_3`, and by Theorem 4 it cannot be witnessed in `H_4` by pour route changes.
- **Where the `H_3` work concentrates.** In `H_3` the pour telescopes:
  `E^c_(a,b)(m) = u_(m-1) ⋯ u_0` freely (with letter conversions), where
  `u_j = λ_ac^j λ_ab λ_ca^j`. As a permutation, `u_j = c_j λ_ab` with `c_j` the cycle
  `(a,j+1) -> (a,1) -> (a,2) -> ... -> (a,j+1)`: it is a two-ray element. Rewriting
  each `u_j` into two-ray letters by induction on `j`, via
  `u_j = λ_ac u_(j-1) λ_ca`, needs only relations among pushed transpositions on one
  ray, conjugated by `λ_ac`. These are single-ray far-commutation relations of depth
  `<= m` in `H_3`. So `A_3` is controlled by the three-ray far commutation
  `F_3(k) = Area_(H_3)([τ_a, D^b_a(k)])` together with the three-ray transposition
  reroute `D^b_a(k) -> D^c_a(k)`. That is exactly the relation where the recorded
  three-ray attempts give the Tower-of-Hanoi recursion `C(k) <= 2C(k-1) + O(k)`
  (six-ray note, Remark 3.2). This paragraph is a heuristic localisation, not a proof.


