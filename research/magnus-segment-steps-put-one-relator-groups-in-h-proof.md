---
rg: 2
id: magnus-segment-steps-put-one-relator-groups-in-h-proof
kind: route
title: A basis change fixing the Magnus edge group turns each segment step into a root adjunction or a cyclic HNN, and the maps to Z it needs are exactly the solutions of the abelianized recurrence restricted to the top window
target: magnus-segment-steps-put-one-relator-groups-in-h
requires:
  - edge-injective-quotients-give-hughes-free-division-rings
  - vertex-injective-quotients-give-hughes-free-division-rings
---

## Inputs

- **(C)** `𝓗` is closed under subgroups, extensions and directed unions, and contains free groups. This is item 1 of
  [[vertex-injective-quotients-give-hughes-free-division-rings]]. Groups in `𝓗` are locally indicable, hence
  torsion-free.
- **(E1)** The edge-injective quotient lemma. If a graph of groups has vertex groups in `𝓗` and maps to some
  `Q ∈ 𝓗` injectively on every edge group, then it lies in `𝓗`. This is item 1 of
  [[edge-injective-quotients-give-hughes-free-division-rings]].
- **(E2)** Let `S ∈ 𝓗`, let `a, c ∈ S`, and let `f: S -> Z` have `f(a) f(c) ≠ 0`. Then `S *_{a ↦ c} ∈ 𝓗`
  (item 2 there).
- **(E3)** Let `S ∈ 𝓗`, `g ∈ S` and `k ≥ 1`, and let `f: S -> Z` have `f(g) ≠ 0`. Then `S *_{g = s^k} <s> ∈ 𝓗`
  (item 3 there).
- **(M)** Magnus–Moldavanskii. Let `r'_j` be the shift of `r'` by `j`, and
  `S_[p,n] = <a_p, …, a_{n+m} | r'_p, …, r'_n>`, so that `S_[p,p-1]` is free on `a_p, …, a_{p+m-1}`.
  - The *top window* `W_n = <a_{n+1}, …, a_{n+m}>` is free of rank `m` in `S_[p,n]`, and also in
    `B_{n+1} = <a_{n+1}, …, a_{n+1+m} | r'_{n+1}>` (Freiheitssatz).
  - `S_[p,n+1] = S_[p,n] *_{W_n} B_{n+1}`.
  - `N = ker(G -> Z)` is the directed union of the `S_[p,n]`, and the shift by `t` gives
    `S_[p,n] ≅ S_[0,n-p]`.

## The window space

A homomorphism `S_[0,n] -> Q` is a vector `(x_0, …, x_{n+m}) ∈ Q^{n+m+1}` with `Σ_{i=0}^m e_i x_{j+i} = 0` for
`0 ≤ j ≤ n`. Let `M_{n+1} ⊆ Q^m` be the set of its top windows `(x_{n+1}, …, x_{n+m})`. So `M_0 = Q^m`, since
`S_[0,-1]` is free.

**Recursion.** A solution for `j ≤ n` restricts to a solution for `j ≤ n - 1`, with window
`(x_n, …, x_{n+m-1}) ∈ M_n`. Conversely, a vector in `M_n`, extended by any `x_{n+m}` with
`Σ_i e_i x_{n+i} = 0`, comes from a solution. So `M_{n+1} = Φ(M_n)`, where `Φ(M)` is the set of
`(w_1, …, w_m)` such that `(w_0, …, w_{m-1}) ∈ M` and `Σ_i e_i w_i = 0` for some `w_0`.

**Stabilization.** `Φ` is monotone and `M_1 ⊆ M_0`, so by induction `M_{n+1} ⊆ M_n`. A decreasing chain of
subspaces of `Q^m` whose dimension stays the same for one step is constant from then on, since
`M_{n+1} = M_n` gives `M_{n+2} = Φ(M_{n+1}) = Φ(M_n) = M_{n+1}`. So the chain is constant from some
`n_0 ≤ m + 1` on, with value `M_∞`, and `M_∞ ⊆ M_{n+1}` for every `n`.

**The test.** Let `c ∈ Q^m`, read as the functional `w ↦ c · w`. For `v ∈ F(W_n)`, the value of a homomorphism
`S_[0,n] -> Q` on `v` is `c_v` applied to its window, where `c_v` is the exponent vector of `v` in the letters
`a_{n+1}, …, a_{n+m}`.
- So some `f: S_[0,n] -> Z` has `f(v) ≠ 0` if and only if `c_v` does not vanish on `M_{n+1}` (clear
  denominators).
- This holds for every `n` if and only if `c_v` does not vanish on `M_∞`.
- For two elements `v, v'`, one `f` works for both as soon as each functional is nonzero on `M_{n+1}`. The
  vectors where either functional vanishes form two proper subspaces, and a vector space over `Q` is not the
  union of two proper subspaces.

## Item 1: the segment step

Take the top case. For the bottom case, replace `t` by `t^{-1}`, which reverses the indices and turns bottom
steps into top steps. By (M) and the shift, it is enough to prove `S_[0,n] ∈ 𝓗` for every `n ≥ -1`. Then
`N ∈ 𝓗` by (C), since it is a directed union of copies of these, and `G = N ⋊ Z ∈ 𝓗` by (C).

We use induction on `n`. `S_[0,-1]` is free. Fix `n ≥ -1` and assume `S = S_[0,n] ∈ 𝓗`.
- Put `B = B_{n+1}` and `W = W_n`. Write `α_{n+1}, β_{n+1}, u_{n+1}, x_{n+1}, y_{n+1}` for the shifts by `n+1`
  of `α, β, u, x, y`. These are words in `W`.
- The substitution `a_{n+1+m} ↦ α_{n+1}^{-1} σ β_{n+1}^{-1}` is an automorphism of the free group
  `F(a_{n+1}, …, a_{n+1+m})` that fixes `W` pointwise. So `B = <W, σ | r''_{n+1}>`, with `W` embedded as before.

**Root form.** Here `r''` is conjugate to `σ^k u^{-1}`, so `B = W *_{u_{n+1} = σ^k} <σ>`, and
`S_[0,n+1] = S *_W B = S *_{u_{n+1} = σ^k} <σ>`.
- If `|k| = 1` this is just `S`.
- Otherwise, by the test, some `f: S -> Z` has `f(u_{n+1}) ≠ 0`, and (E3) gives `S_[0,n+1] ∈ 𝓗`.
- The sign of `k` does not matter, since `σ ↦ σ^{-1}` is an automorphism.

**Hnn form.** Here `r''` is conjugate to `σ^{-1} x σ y`, so `σ^{-1} x_{n+1} σ = y_{n+1}^{-1}` holds in `B`.
- `B` is the HNN extension of `W` with cyclic edge groups `<x_{n+1}>` and `<y_{n+1}>`. These are infinite cyclic
  in the free group `W`, since `x` and `y` are nonempty reduced words.
- Amalgamating it with `S` over `W` gives the HNN extension `S_[0,n+1] = S *_{x_{n+1} ↦ y_{n+1}^{-1}}` with
  stable letter `σ`.
- By the test, one `f: S -> Z` has `f(x_{n+1}) ≠ 0` and `f(y_{n+1}) ≠ 0`. Then (E2) gives `S_[0,n+1] ∈ 𝓗`.

So every `S_[0,n]` is in `𝓗`, and hence so is `G`. ∎

## Item 2

If `e_m ≠ 0`, then for any `(w_0, …, w_{m-1})` the relation `Σ_i e_i w_i = 0` can be solved for `w_m`. So
`Φ(Q^m) = Q^m` and `M_∞ = Q^m`.
- With `α = β = 1` and `a_m` in one syllable `a_m^k`, the root form holds with `k = e_m`, `u = v^{-1}`, and the
  hypothesis becomes `c_u ≠ 0`. That is `(e_0, …, e_{m-1}) ≠ 0`, the hypothesis of the root-tower theorem.
- In the hnn form, `σ` has exponent sum `0`. The substitution preserves the exponent of the top letter, so
  `e_m = 0`.
- For `e = (0, ±1, 0)`: `Φ(Q^2)` is `{(w_1, w_2) : w_1 = 0}`, and `Φ` of that is the same line. So
  `M_∞ = {(0, w)}`.

## Item 3: the computation

Run it from `experiments/one-relator-hughes-free-char-p-2026-09-17/`:
- `python3 segment_certify.py` writes `words-L11.txt`.
- `python3 segment_certify.py census 12` writes `census-L12.txt`. It is single-threaded and takes about 2 minutes.

**How it works.** The script imports the landed certifier
`experiments/magnus-hnn-vertex-quotients-2026-09-17/hierarchy_certify.py` unchanged, and extends its root-tower
test by rule 1.
- The rule is `top_step`. For all `α, β` of length at most 2 in `F(A)`, it substitutes, cyclically reduces, and
  rotates to start at a `σ`-syllable.
- It then checks for the root form (one `σ`-syllable) or the hnn form (two `σ`-syllables of exponents `±1`
  with opposite signs).
- It tests the functionals against `window_space(e)`. That function computes `M_∞` by the recursion above, with
  exact `Fraction` arithmetic, stopping when the dimension stops dropping.
- The bottom case applies the same routine to the index-reversed rewrite.
- Every certificate therefore rests on item 1 and on the landed rules: free, Nielsen, retraction, root rule,
  bs-quotient and root tower.

**Census counts.** Words are taken up to rotation, inversion and relabelling, and proper powers are dropped.

| length | open under the landed rules | certified by rule 1 | open after rule 1 |
|---|---|---|---|
| ≤ 10 | 0 | 0 | 0 |
| 11 | 8 | 6 | 2 |
| 12 | 73 | 63 | 10 |

The open counts under the landed rules match `census-L11.txt` and item 7 of the edge-injective node, which is a
check on the harness.

**The survivors.** These are the relators listed in `census-L12.txt`, with the Magnus rewrite of each Nielsen normal form, as printed by `trace` in `segment_certify.py`:

| relator | Magnus rewrite | same group as |
|---|---|---|
| `A A B a b a B A A b b` | `X0x1X2x0x2` | (length 11, `r_6`) |
| `A A B B A A b a B a b` | `X0X2x0X1x2` | (length 11, `r_8`) |
| `A A A B B a b A b a a B` | `X0X1X2x0X1x2x1` | |
| `A A A B a a b b b a a B` | `X0X1X2x1x0x2x1` | |
| `A A A B a a b A b a B B` | `X0X1X2x1x0X1x2` | |
| `A A A b b a B A B a a b` | `X2X1X0x2X1x0x1` | |
| `A A A b a a B B B a a b` | `X2X1X0x1x2x0x1` | |
| `A A A b a a B A B a b b` | `X2X1X0x1x2X1x0` | |
| `A A B A B A A b a B a b` | `X0X2x0X1x2` | `r_8` |
| `A A B a B A A b a B a b` | `X1X2x1X0X1x2x0` | |
| `A A B a b a B A A b A b` | `X0x1X2x0x2` | `r_6` |
| `A A B a b a B A A b a b` | `X2X1x0x2X1X0x1` | |

Each of them has `e = (0, ±1, 0)` and `M_∞ = {(0, w)}`.

## Item 4: the obstruction for `r_6` and `r_8`

**Segment abelianizations.** For `e = (0, ε, 0)`, the relations of `S_[0,n]` in `H_1` read `ε x_{j+1} = 0` for
`0 ≤ j ≤ n`. So `H_1(S_[0,n]) = Z^2`, on `a_0` and `a_{n+2}`, and every `f: S_[0,n] -> Z` kills
`a_1, …, a_{n+1}`. In particular it kills `a_{n+1}`, the first letter of the top window.

**Every twist.** Let `α, β ∈ F(a_0, a_1)` be arbitrary, and substitute into the top letter:
- `r_6`, top: `a_0^{-1} a_1 a_2^{-1} a_0 a_2` becomes, cyclically, `σ^{-1} (α a_0 α^{-1}) σ (β^{-1} a_0^{-1} a_1 β)`.
  So `x = α a_0 α^{-1}`.
- `r_8`, top: `a_0^{-1} a_2^{-1} a_0 a_1^{-1} a_2` becomes `σ^{-1} (α a_0 a_1^{-1} α^{-1}) σ (β^{-1} a_0^{-1} β)`.
  So `y = β^{-1} a_0^{-1} β`.

For the bottom, reverse the indices (`p ↦ 2 - p`), which gives `X2x1X0x2x0` and `X2X0x2X1x0`, and substitute
into the new top letter:
- `r_6`, bottom: `σ^{-1} (α a_1 a_0^{-1} α^{-1}) σ (β^{-1} a_0 β)`, so `y = β^{-1} a_0 β`.
- `r_8`, bottom: `σ^{-1} (α a_0^{-1} α^{-1}) σ (β^{-1} a_1^{-1} a_0 β)`, so `x = α a_0^{-1} α^{-1}`.

In each case the two `σ`-letters cannot cancel, because the words between them are conjugates of nontrivial
elements. So the word is always in hnn form, never in root form. One edge element is a conjugate of
`a_0^{±1}`, whose functional `(±1, 0)` vanishes on `M_∞ = {(0, w)}`. In the reversed coordinates the exponent
vector is again `(0, ±1, 0)`. So rule 1 fails for every `α, β`, in both directions.

The same computation shows more. At every level `n`, one of the two edge elements of the HNN
`S_[0,n+1] = S_[0,n] *_σ` is killed by every map `S_[0,n] -> Z`. So neither (E2) nor (E3) can make that step.

## Item 5: the exact HNN criterion

Let `G = B *_{σ^{-1} x σ = y}` with `B ∈ 𝓗` and `x ≠ 1`, so `x` has infinite order by (C).
- **If.** Define `G -> Q` by `φ` on `B` and `σ ↦ τ`. It respects the relation, since `τ^{-1} φ(x) τ = φ(y)`.
  It is injective on the edge group `<x>`, since `φ(x)` has infinite order. (E1) with the single vertex group
  `B` gives `G ∈ 𝓗`.
- **Only if.** Take `Q = G`, `φ` the inclusion and `τ = σ`.
- (E2) is the case `Q = Z[1/(f(a)f(c))] ⋊ Z`. There `φ` is `f` followed by the inclusion `Z -> Z[1/…]`, and `τ`
  is the generator of the `Z` factor.

**Why the shift is circular for `r_6`.** In `S_[-2,n-1]`, the relation `r'_{n-1}` gives
`a_{n+1}^{-1} a_{n-1} a_{n+1} = a_n^{-1} a_{n-1}`. So the shift `S_[0,n] -> S_[-2,n-2] ⊂ S_[-2,n-1]` by `-2`,
with `τ = a_{n+1}`, satisfies the criterion. But its target is isomorphic to `S_[0,n+1]`, the group to be shown in
`𝓗`. ∎
