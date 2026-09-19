# Houghton H_3: the reroute family is a two-ray commutation in disguise, and the other four families conjugate down to it

Lane swarm-0917-w12-w12-z-last1, 2026-09-18. Zaremsky Problem 1.24, hole
`houghton-h3-five-three-ray-families-have-polynomial-area`. Status: complete proof, with
every derivation machine-checked for small indices by
`experiments/houghton-h3-families-2026-09-17/verify_h3_families.py`. Unreviewed.

**Result.** For the five families of Theorem A of
`research/artifacts/zp-houghton-three-rays-2026-09-18.md` (the *three-ray note*):

```text
R_3(k)   <= 2 A(k) + |N_k| + 4k + 2,
F_3, B_3, C_3, D_3  <=  6 max_(m <= 2k) R_3(m) + O(k)     (indices <= k).
```

Here `A(k)` and `N_k` are those of Proposition 5 of
`research/artifacts/zp-houghton-pour-doubling-2026-09-18.md` (the *doubling note*). So
`Φ(k) ≼ k^(5 + log_2 K) log k`. By Theorem A, `δ_(H_3)` is polynomially bounded.

## 0. Conventions and the two inputs

The conventions are those of `research/artifacts/zp-houghton-pours-2026-09-17.md` §0,
with `n = 3` and rays `{1,2,3}`.

- Permutations act on the right, and words are read left to right.
- `λ_xy` pulls ray `x` in and pushes ray `y` out. `τ_x = ((x,1),(x,2))`.
- `D^u_x(m) = λ_xu^m τ_x λ_ux^m` represents `((x,m+1),(x,m+2))`. In particular
  `D^u_x(0) = τ_x` for either `u`.
- `P` is the finite presentation of §0 there. It contains the set `Q` of all trivial
  words of length `<= 40` in `λ_xy^(±1), τ_x^(±1)`, and `Area = Area_P`.
- The commutator is `[U,V] = U V U^(-1) V^(-1)`.

A *route function* `c` is fixed, and `Ed(t_x(j)) = D^(c(x))_x(j-1)`. The top-edge word
is `Ed(σ_{p,q}) = λ_qp τ_p λ_pq`, which represents `((p,1),(q,1))`. Here `p` is the
smaller index, but the proofs below work for either order.

**Moves.** A derivation rewrites a word to the empty word. Each move costs as follows.

- *Free* moves are free reduction, cyclic permutation, and conjugation of the whole word
  by any word. They cost 0.
- A *Q-step* replaces a subword `u` by `v`, where `u = v` in `H_3` and
  `|u| + |v| <= 40`. Then `u v^(-1) ∈ Q`, so the step costs 1. Two special cases:
  - A *conversion* turns a formal inverse into a positive letter: `λ_xy^(-1) -> λ_yx`
    or `τ_x^(-1) -> τ_x`.
  - A *swap* is `τ_x ℓ -> ℓ τ_x`, for a letter `ℓ` whose ray support misses ray `x`.
- A *macro* replaces `u` by `v`, where `u v^(-1)` is a word of one of the families.
  It costs that family's area, using `Area(W_1 u W_2) <= Area(W_1 v W_2) + Area(u v^(-1))`.

The *ray support* of `λ_ab` is `{a,b}`. The ray support of `τ_a` is `{a}`.

**Input 1: Theorem A of the three-ray note, quoted.** It is established as
`houghton-h3-dehn-polynomial-iff-five-three-ray-families`.

- The families are defined "for `k, i, j >= 0`", "each maximised over all labelings of
  the rays with the stated distinctness":
  - `F_3(k) = [τ_x, D^(c(x))_x(k)]`;
  - `R_3(k) = D^u_x(k) · D^v_x(k)^(-1)`, with `{x,u,v} = {1,2,3}`;
  - `B_3(i,j) = [Ed(t_x(i)), Ed(t_y(j))]`, with `x != y`;
  - `C_3(j) = [Ed(σ_{x,y}), Ed(t_z(j))]`, with `σ_{x,y}` and `t_z(j)` vertex-disjoint;
  - `D_3(j) = λ_wz · Ed(t_x(j)) · λ_zw · Ed(t_x(j))^(-1)`, with `{x,z,w} = {1,2,3}`.
- `Φ(k) = max over i, j <= k of { F_3(i), R_3(i), B_3(i,j), C_3(j), D_3(j) }`.
- The theorem: "`Φ(L) <= δ_(H_3)(C L)` and `δ_(H_3)(L) <= C L^6 ( Φ(L + C) + L )`.
  … If `Φ(k) ≼ k^d` with `d >= 1`, then `δ_(H_3)(x) ≼ x^(6+d)`."

Only null-homotopic members count, and a family's area is the maximum over them.

- `F_3(k)` is null-homotopic exactly for `k = 0` and `k >= 2`. For `k = 1` the two
  transpositions overlap.
- `C_3(j)` with `z` an endpoint of the top edge needs `j >= 2`.

**Input 2: Proposition 5 of the doubling note, quoted.** It is established as
`houghton-three-ray-pours-have-polynomial-two-ray-normal-forms`.

- For rays `a,b,c` there are words `N_m` in the two-ray letters `λ_ab, λ_ba, τ_a, τ_b`.
  They are given by `N_1 = λ_ab`, `N_(2m) = Δ̂(N_m)` and `N_(2m+1) = ψ(N_(2m)) λ_ab`.
- `N_m` represents `λ_ac^m λ_cb^m`, and `|N_m| <= m^5`.
- `A(m) = Area( λ_ac^m λ_cb^m · N_m^(-1) )`, and "`A(m) <= 4 (1 + log_2 m) · m^(5 + log_2 K)`
  for all `m >= 1`".
- The statement is made for one labeling `(a,b,c)`. Relabeling the rays gives it for
  every labeling, with the constant `K` of that labeling. Theorem 6 of the doubling note
  uses it this way: "`W_4(m) <= 2 K_1 · max A(m)`, where the max is over the 24
  labelings. Proposition 5 bounds each `A(m)`".
- Write `Ā(m)` for the maximum of `A(m')` over the six labelings of `H_3` and all
  `m' <= m`, and `K_max` for the largest `K`.

**Why this escapes Lemma C.1 of the three-ray note.** Lemma C.1 says that for members of
`B_3, C_3, D_3, F_3`, any two words representing *the two commuting parts* have
intersecting ray supports. The arguments below never reroute the given parts. They first
conjugate the whole relation by a pull `λ^m`. That turns it into a commutation whose
single-letter part is `τ_y` (index 1), and a single letter has ray support of size 1.
After a reroute, the other part avoids that ray. For `R_3`, which C.1 does not cover,
the two-ray word `N_k` does the same job.

## 1. The reroute family

**Lemma 1.** Let `{x,u,v} = {1,2,3}` and `k >= 1`. Let `N_k` be the word of Input 2
for the labeling `(a,b,c) = (u,v,x)`. Then

```text
Area( D^u_x(k) · D^v_x(k)^(-1) ) <= 2 A_(u,v,x)(k) + |N_k| + 4k + 2.
```

Hence `R_3(k) <= 2 Ā(k) + k^5 + 4k + 2`.

*Proof.*

1. **Convert** the `2k + 1` inverse letters of `D^v_x(k)^(-1)`. The word becomes
   `λ_xu^k τ_x · M · τ_x λ_vx^k`, where `M = λ_ux^k λ_xv^k`. This is literally the pour
   from `u` to `v` through `x`.
2. **Replace** `M` by `N_k`. This is one relation of Input 2 for the labeling `(u,v,x)`,
   so it costs `A(k)`.
3. **Swap.** `N_k` uses only `λ_uv, λ_vu, τ_u, τ_v`, whose ray supports miss ray `x`.
   So `τ_x` moves right across `N_k` in `|N_k|` swaps. One Q-step then deletes
   `τ_x τ_x`.
4. **Replace** `N_k` by `M` again, at cost `A(k)`. The word is `λ_xu^k λ_ux^k λ_xv^k λ_vx^k`,
   and `2k` Q-steps cancel the adjacent inverse pairs.

The total is `2A(k) + (2k+1) + |N_k| + 1 + 2k`. ∎

This bypasses the triangle word `X_k^2` of §5 of the doubling note. That section put
`τ_x` between two *different* pours and was left with `Area(X_k^2)`. Here the product
of the two middle half-pours is itself one pour between the two route rays. Its two-ray
normal form avoids ray `x`.

## 2. Same-ray commutation

For `x != u` and `k >= 0`, let `F'(k)` be the largest area of
`τ_x D^u_x(k) τ_x D^u_x(k)`, taken over labelings. This word is trivial for `k = 0`
and `k >= 2`.

**Lemma 2.** For `k >= 2`, `F'(k) <= 2 R_3(k-2) + 4k`. For `k ∈ {0} ∪ [2,∞)`,
`F_3(k) <= F'(k) + 2k + 2`.

*Proof.*

1. **Conjugate** by `λ_ux^2` and convert the two trailing inverses (2 Q-steps). Split
   `λ_xu^k = λ_xu^2 λ_xu^(k-2)` and `λ_ux^k = λ_ux^(k-2) λ_ux^2`. With `m = k - 2`, the
   word is literally

   ```text
   [λ_ux^2 τ_x λ_xu^2] · λ_xu^m τ_x λ_ux^m · [λ_ux^2 τ_x λ_xu^2] · λ_xu^m τ_x λ_ux^m · [λ_ux^2 λ_xu^2].
   ```

2. **Collapse the brackets.** `λ_xu^2` sends `(x,1) -> (u,2)` and `(x,2) -> (u,1)`, so
   `λ_ux^2 τ_x λ_xu^2 = τ_u`. Replacing each of the first two brackets by `τ_u` is one
   Q-step, since `u v^(-1)` has length 6. Deleting the last bracket is one more.
3. The word is now `τ_u D^u_x(m) τ_u D^u_x(m)`. With `w` the third ray, **reroute**
   both copies to `D^w_x(m)`. This costs `2 R_3(m)`, and nothing if `m = 0`.
4. **Commute.** `D^w_x(m)` has ray support `{x,w}`, which misses `u`. Take `2m + 1`
   swaps to move `τ_u` across, one Q-step for `τ_u τ_u`, and `2m + 1` Q-steps to cancel
   `D^w_x(m) D^w_x(m)` from the middle out.

The total is `(2 + 3) + 2(2m+1) + 1 = 4k` Q-steps, plus `2 R_3(k-2)`. Finally,
`F_3(k) = τ_x D τ_x^(-1) D^(-1)` becomes the `F'` word after `2k + 2` conversions. ∎

## 3. The letter family D_3

**Lemma 3.** `D_3(j) <= R_3(j) + R_3(j-1) + 4` for `j >= 1`.

*Proof.* The word is `λ_wz V λ_zw V^(-1)`, with `V = D^c_x(j-1)` and `c = c(x) ∈ {z,w}`.

1. **Split the two outer letters** (2 Q-steps): `λ_wz -> λ_wx λ_xz` and
   `λ_zw -> λ_zx λ_xw`. These are pour identities `λ_ac λ_cb = λ_ab`.
2. **Reroute** `V` to `D^z_x(j-1)`. This costs `R_3(j-1)`, and nothing if `c = z`.
3. **Push.** `λ_xz D^z_x(j-1) λ_zx` is literally `D^z_x(j)`. Reroute it to `D^w_x(j)`,
   at cost `R_3(j)`.
4. **Pull** (2 Q-steps). The word is `λ_wx · λ_xw^j τ_x λ_wx^j · λ_xw · V^(-1)`. Cancel
   the leading `λ_wx λ_xw`, then the pair `λ_wx λ_xw` at position `2j - 1`. What remains
   is `D^w_x(j-1) V^(-1)`.
5. **Reroute back** to `D^c_x(j-1)`. This costs `R_3(j-1)`, and nothing if `c = w`.
   Then the word cancels freely.

Exactly one of the reroutes in steps 2 and 5 is nontrivial. ∎

## 4. Ray edges on different rays: B_3

**Lemma 4.** For `x != y`, `i, j >= 1` and `z` the third ray,

```text
B_3(i,j) <= 2R_3(i-1) + 2R_3(j-1) + 2R_3(i+j-2) + 6(i+j) + 2j - 9.
```

*Proof.* Put `U = D^(c(x))_x(i-1)` and `V = D^(c(y))_y(j-1)`.

1. **Convert** `U^(-1) V^(-1)`. This takes `2(i+j) - 2` Q-steps and gives `U V U V`.
2. **Reroute** both `U`s to `D^y_x(i-1)` and both `V`s to `D^x_y(j-1)`. This costs
   `2R_3(i-1) + 2R_3(j-1)`.
3. **Conjugate** by `λ_xy^m`, with `m = j - 1`, and convert the `m` trailing inverses.
   Since `D^x_y(m) = λ_yx^m τ_y λ_xy^m`, the word is **literally**

   ```text
   λ_xy^m · λ_xy^(i-1) τ_x λ_yx^(i-1) · λ_yx^m τ_y λ_xy^m · λ_xy^(i-1) τ_x λ_yx^(i-1) · λ_yx^m τ_y λ_xy^m · λ_yx^m
     =  D^y_x(n) · τ_y · D^y_x(n) · τ_y · λ_xy^m λ_yx^m ,        n = i + j - 2.
   ```

4. **Cancel the tail** in `m` Q-steps and permute cyclically. The result is
   `τ_y D^y_x(n) τ_y D^y_x(n)`, a commutation of the single letter `τ_y` with
   `((x,n+1),(x,n+2))`.
5. **Reroute** both copies to `D^z_x(n)`, at cost `2R_3(n)`. Its ray support `{x,z}`
   misses `y`, so commute as in Lemma 2, step 4. That takes `2(2n+1) + 1` Q-steps. ∎

## 5. A top edge and a ray edge: C_3

**Lemma 5.** Let `σ = σ_{p,q}` have `τ`-ray `p`, let `r` be the third ray, and let
`t_z(j)` be vertex-disjoint from `σ`. Then

```text
C_3(j) <= 2R_3(j-1) + max{ 2D_3(j), F'(j), 2R_3(j-2) } + 6j + 3.
```

*Proof.* Put `U = λ_qp τ_p λ_pq` and `V = D^(c(z))_z(j-1)`.

1. **Convert** `U^(-1) V^(-1)` (`2j + 2` Q-steps), giving `U V U V`.
2. **Conjugate** by `λ_pq`, convert one letter, and cancel `λ_pq λ_qp` at the front
   (2 Q-steps). The word is `τ_p S τ_p S`, with `S = λ_pq V λ_qp`.

There are three cases.

- **`z = r`, `j >= 1`.** `S V^(-1)` is literally a `D_3(j)` word, with `x = r`,
  `w = p`, `z = q`. So `S -> V` costs `D_3(j)`, twice. Then reroute both `V`s to
  `D^q_r(j-1)`, at cost `2R_3(j-1)`. It misses ray `p`, so commute in `4j - 1` Q-steps.
- **`z = p`, `j >= 2`.** Reroute both `V`s to `D^q_p(j-1)`, at cost `2R_3(j-1)`. Now
  `S = λ_pq D^q_p(j-1) λ_qp = D^q_p(j)` literally. The word
  `τ_p D^q_p(j) τ_p D^q_p(j)` costs `F'(j)`.
- **`z = q`, `j >= 2`.** Reroute both `V`s to `D^p_q(j-1)`, at cost `2R_3(j-1)`. In each
  `S = λ_pq λ_qp^(j-1) τ_q λ_pq^(j-1) λ_qp`, cancel the outer pairs (4 Q-steps in
  total), so `S -> D^p_q(j-2)`. Reroute to `D^r_q(j-2)`, at cost `2R_3(j-2)`. It misses
  `p`, so commute in `4j - 5` Q-steps.

Each case uses at most `6j + 3` Q-steps. ∎

## 6. Conclusion

Let `R̄(k) = max_(m <= k) R_3(m)`. For `i, j <= k`, Lemmas 1–5 give the following
bounds.

| family | bound |
|---|---|
| `R_3(i)` | `R̄(k)` |
| `F_3(i)` | `2R̄(k) + 6k + 2` |
| `D_3(j)` | `2R̄(k) + 4` |
| `B_3(i,j)` | `6R̄(2k) + 14k` |
| `C_3(j)` | `2R̄(k) + max{4R̄(k) + 8, 2R̄(k) + 4k, 2R̄(k)} + 6k + 3 <= 6R̄(k) + 10k + 11` |

So `Φ(k) <= 6 R̄(2k) + 14k + 11`. By Lemma 1 and Input 2,

```text
R̄(2k) <= 2Ā(2k) + (2k)^5 + 8k + 2 <= 8 (2 + log_2 k) (2k)^(5 + log_2 K_max) + (2k)^5 + 8k + 2.
```

Hence `Φ(k) ≼ k^(5 + log_2 K_max) log k`. With any integer `d > 5 + log_2 K_max`, we
get `Φ(k) ≼ k^d`. Theorem A then gives

```text
δ_(H_3)(x) ≼ x^(6 + d).
```

This closes `houghton-group-h3-has-polynomial-dehn-function`, through the route
`houghton-h3-polynomial-dehn-via-five-families`. Together with
`houghton-groups-with-five-or-more-rays-have-polynomial-dehn` and
`houghton-group-h4-has-polynomial-dehn-function`, the route
`houghton-polynomial-dehn-by-ray-count` gives that **every Houghton group `H_n`,
`n >= 3`, has polynomially bounded Dehn function**.

This is the polynomial half of Zaremsky Problem 1.24. The quadratic question is
untouched. The exponent is not explicit, because of `log_2 K`.

## 7. Machine check

`experiments/houghton-h3-families-2026-09-17/verify_h3_families.py` has no
dependencies and runs in a few seconds. Its output is saved as `verify_h3_families.out`.
The script represents words as lists of signed letters and runs every derivation above
literally.

- A Q-step is accepted only if the two sides are equal in `H_3` and have total length
  `<= 40`.
- A macro is accepted only if its two sides are literally the two sides of the cited
  relation (`A`, `R_3`, `D_3` or `F'`) and are equal in `H_3`.
- Equality is decided on every point of depth `<= max(|u|,|v|) + 3`.
- Each derivation must end at the empty word, and its Q-step count must stay within the
  stated bound.

It checks the following, 4986 derivations in all:

- `N_k` for all 6 labelings, `k <= 12`;
- `R_3` and `F'` for all labelings, `k <= 12`;
- for all 8 route functions:
  - `F_3` for `k ∈ {0, 2, …, 12}`;
  - `D_3` for `j <= 12`;
  - `B_3` for `i, j <= 7`;
  - `C_3` for every `(p,q,z)`, `j <= 12`.

The proofs are uniform in the indices. The script confirms the index bookkeeping, the
literal matches and the Q-step identities. It does not check the areas of the macros,
which are Inputs 1 and 2.
