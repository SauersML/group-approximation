# Infinite-order elements of V have hyperbolic periodic points: a direct proof

Swarm lane `zaremsky-2-15b` (swarm-zaremsky-2-15b-bi-orderable-su), 2026-09-16. This is a
self-contained proof of the statement of claim
`infinite-order-elements-of-v-have-hyperbolic-periodic-points` (called (V0) in
`research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part3.md`). When it was
written, another agent held the advisory lock on that claim, so this lane added no route. A
route with `requires: []` can cite this artifact once the proof has been checked.

The proof fills the two gaps named in that claim's Attempts section. The first is the case
where cone lengths grow without nesting. A pigeonhole argument on record times of the
length cocycle handles it (Lemma 2). The second is the global "finite order" conclusion. A
finiteness count handles it (Lemma 1).

## Setting and notation

`C = {0,1}^ω`. Words are finite binary strings, `|w|` is the length, and `wC` is the cone
of all infinite sequences beginning with `w`. An element `g` of `V` is given by complete
prefix codes `u_1, ..., u_n` and `v_1, ..., v_n` with `g(u_i y) = v_i y` for all `y` in `C`.

**Affine on a word.** `g` is *affine on* `w` if some word `g_*(w)` satisfies
`g(w y) = g_*(w) y` for all `y` in `C`. This word is unique. Suppose `a y = b y` for all
`y` with `|a| < |b|`. Then `b = a c` with `c` nonempty and `y = c y` for all `y`, which
fails for any `y` whose first letter differs from that of `c`.

Put `N = max_i max(|u_i|, |v_i|)` and `D = max_i ||u_i| − |v_i||`. These constants are the
same for `g^{-1}`, which has pieces `v_i ↦ u_i`.

**(F1)** If `|w| ≥ N`, then `g` and `g^{-1}` are affine on `w`, and `|g_*(w)|` differs from
`|w|` by at most `D`.
*Proof.* Any infinite extension of `w` has a unique prefix `u_i` in the complete code.
Since `|u_i| ≤ N ≤ |w|`, that `u_i` is a prefix of `w`. Writing `w = u_i w'` gives
`g(w y) = v_i w' y`. The same argument with the code `{v_i}` works for `g^{-1}`. ∎

**(F2)** If `g` is affine on `w`, then it is affine on every extension `w r`, with
`g_*(w r) = g_*(w) r`. If `h` is affine on `w` and `k` is affine on `h_*(w)`, then `k h` is
affine on `w`, with `(k h)_*(w) = k_*(h_*(w))`. If `g` is affine on `w` with image `w'`,
then `g^{-1}` is affine on `w'` with image `w`. All three are immediate.

**Length cocycle.** For `x` in `C`, let `λ(x) = |w| − |g_*(w)|` for any prefix `w` of `x`
on which `g` is affine. Such prefixes exist by (F1). Two of them are comparable, and by
(F2) the longer one `w r` has image `g_*(w) r`, so it gives the same value. Hence `λ` is
well defined and `|λ| ≤ D`. Put `S_0(x) = 0` and `S_k(x) = Σ_{0 ≤ i < k} λ(g^i x)`.

**(F3)** Let `k ≥ 1`. If `g^k` is affine on a prefix `w` of `x`, then
`|w| − |(g^k)_*(w)| = S_k(x)`.
*Proof.* Induction on `k`. The case `k = 1` is the definition. For `k ≥ 2`, choose a
prefix `w'` of `x` that extends `w`, on which `g^{k−1}` is affine, and whose image
`(g^{k−1})_*(w')` has length at least `N`. Such a `w'` exists: take any prefix on which
`g^{k−1}` is affine and extend it, since by (F2) extending the domain word extends the
image word. By (F1) and (F2), `g^k` is affine on `w'`, and its image is
`g_*((g^{k−1})_*(w'))`. By uniqueness of images and (F2), this image is `(g^k)_*(w) r`,
where `w' = w r`. So `w'` and `w` give the same length difference. That difference
splits as `(|w'| − |(g^{k−1})_*(w')|) + (|(g^{k−1})_*(w')| − |g_*((g^{k−1})_*(w'))|)`.
By induction this equals `S_{k−1}(x) + λ(g^{k−1} x) = S_k(x)`, because
`(g^{k−1})_*(w')` is a prefix of `g^{k−1} x` on which `g` is affine. ∎

So if `g^k(p) = p`, the slope used in claim V0 and in Lemma V-A of part 3 is
`(g^k)'(p) = 2^{S_k(p)}`. If moreover `g^q(p) = p`, the sum defining `S` is `q`-periodic
along the orbit of `p`, so `S_{jq}(p) = j·S_q(p)`.

**(F4)** Write `λ^-` and `S^-` for the cocycle of `g^{-1}`. Then `λ^-(y) = −λ(g^{-1} y)`,
and `S^-_k(g^k x) = −S_k(x)`.
*Proof.* Let `w` be a prefix of `g^{-1} y` on which `g` is affine. Then `g_*(w)` is a
prefix of `y` on which `g^{-1}` is affine with image `w`, which gives
`λ^-(y) = |g_*(w)| − |w| = −λ(g^{-1} y)`. Summing,
`S^-_k(g^k x) = Σ_{i<k} λ^-(g^{k−i} x) = −Σ_{i<k} λ(g^{k−i−1} x) = −S_k(x)`. ∎

## Lemma 1 (bounded cocycle implies finite order)

If some `K ≥ 0` has `|S_k(x)| ≤ K` for all `k ≥ 0` and all `x` in `C`, then `g` has finite
order.

*Proof.* Put `L = N + K`, and let `W` be the set of words of length `L`. We claim by
induction on `k ≥ 0` that for every `w` in `W`, `g^k` is affine on `w` and
`L − K ≤ |(g^k)_*(w)| ≤ L + K`. The case `k = 0` is trivial. Assume the claim for `k`.
The image `(g^k)_*(w)` has length at least `L − K = N`, so `g` is affine on it by (F1).
Hence `g^{k+1}` is affine on `w` by (F2). By (F3), its image has length
`L − S_{k+1}(x) ∈ [L − K, L + K]` for any `x` in `wC`.

`W` is a complete prefix code, so `g^k` is determined by the map `w ↦ (g^k)_*(w)` from `W`
to words of length in `[L − K, L + K]`. There are finitely many such maps, so `g^j = g^k`
for some `j < k`, and `g^{k−j} = 1`. ∎

## Lemma 2 (large positive drift gives a hyperbolic periodic point)

If `S_k(x) > D·(2^N − 1)` for some `x` in `C` and some `k ≥ 1`, then `g` has a periodic
point `p` with least period `q` and `S_q(p) ≠ 0`, that is, `(g^q)'(p) ≠ 1`.

*Proof.* The hypothesis forces `D ≥ 1`. Write `x_m = g^m x` and `s_m = S_m(x)` for
`0 ≤ m ≤ k`. Then `s_0 = 0` and `s_{m+1} − s_m = λ(x_m) ≤ D`.

*Records.* Call `m` a *record* if `s_m > s_{m''}` for every `m'' < m`. So `m = 0` is a
record. List the records as `0 = m_0 < m_1 < ... < m_t`. For `m_j ≤ m < m_{j+1}` the
running maximum `max_{m'' ≤ m} s_{m''}` equals `s_{m_j}`. Therefore
`s_{m_{j+1}} = s_{m_{j+1} − 1} + λ(x_{m_{j+1} − 1}) ≤ s_{m_j} + D`, and so `s_{m_t} ≤ t·D`.
Also `s_{m_t} = max_{m ≤ k} s_m ≥ s_k > D·(2^N − 1)`. Hence `t > 2^N − 1`, so there are at
least `2^N + 1` records. There are only `2^N` words of length `N`, so two records
`m < m'` satisfy `prefix_N(x_m) = prefix_N(x_{m'}) =: w`.

*Pulling back.* Put `c_{m'} = w`. For `m'' = m', m' − 1, ..., m + 1`, put
`c_{m''−1} = (g^{-1})_*(c_{m''})`. We show by downward induction that each `c_{m''}` is a
prefix of `x_{m''}` and `|c_{m''}| = N + s_{m'} − s_{m''} ≥ N`.

This holds for `m'' = m'`. Assume it for `m''`. Since `|c_{m''}| ≥ N`, `g^{-1}` is affine
on `c_{m''}` by (F1). Write `x_{m''} = c_{m''} y_0`. Then
`x_{m''−1} = g^{-1} x_{m''} = c_{m''−1} y_0`, so `c_{m''−1}` is a prefix of `x_{m''−1}`. By
(F2), `g` is affine on `c_{m''−1}` with image `c_{m''}`. So
`λ(x_{m''−1}) = |c_{m''−1}| − |c_{m''}|`, which gives
`|c_{m''−1}| = N + s_{m'} − s_{m''} + (s_{m''} − s_{m''−1}) = N + s_{m'} − s_{m''−1}`.
This is at least `N` because `m''−1 < m'` and `m'` is a record.

*The hyperbolic point.* By (F2), `h = g^{m'−m}` is affine on `c_m` with image `w`. The word
`c_m` is a prefix of `x_m` of length `N + s_{m'} − s_m`. That length is greater than `N`,
since `m < m'` are records and so `s_{m'} > s_m`. Its prefix of length `N` is therefore
`prefix_N(x_m) = w`. Write `c_m = w r` with `r` nonempty, so `|r| = s_{m'} − s_m`.

Then `h(w r y) = w y` for all `y`, so `h^{-1}(w y) = w r y`. The point `p = w r r r ...`
satisfies `h^{-1}(p) = w r (r r ...) = p`, so `h(p) = p`. The word `w r` is a prefix of
`p` on which `h` is affine with image `w`, so `S_{m'−m}(p) = |r| ≥ 1` by (F3). Let `q` be
the least period of `p` under `g`. Then `q` divides `m' − m`, and
`S_{m'−m}(p) = ((m'−m)/q)·S_q(p)`. Hence `S_q(p) ≠ 0`. ∎

## Theorem (V0)

Every element `g` of `V` of infinite order has a periodic point `p` whose least period `q`
satisfies `(g^q)'(p) ≠ 1`. In particular there are `k ≥ 1` and `p` with `g^k(p) = p` and
`(g^k)'(p) ≠ 1`.

*Proof.* Put `K = D·(2^N − 1)`. `g` has infinite order, so by Lemma 1 some `x` and `k`
satisfy `|S_k(x)| > K`. Necessarily `k ≥ 1`, since `S_0 = 0`.

If `S_k(x) > K`, Lemma 2 applies.

Otherwise `S_k(x) < −K`. By (F4), `S^-_k(g^k x) = −S_k(x) > K`, where `S^-` is the cocycle
of `g^{-1}`. The constants `N` and `D` of `g^{-1}` equal those of `g`, so Lemma 2 applied
to `g^{-1}` gives a point `p` of least period `q` under `g^{-1}` with `S^-_q(p) ≠ 0`. Then
`p` has least period `q` under `g` as well. Using (F4) and `g^q p = p`,
`S_q(p) = −S^-_q(g^q p) = −S^-_q(p) ≠ 0`. ∎

## Consequences in the graph (not added by this lane)

With V0 established, the routes `v-excludes-bs-1-n-from-hyperbolic-points` and
`v-nilpotent-abelian-from-hyperbolic-points` have all their prerequisites. Both use only
V0 and Lemma V-A of part 3.

Their targets are `bs-1-n-does-not-embed-in-thompson-v` and
`torsion-free-nilpotent-subgroups-of-thompson-v-are-abelian`. Both also follow from
Burillo–Cleary–Röver (arXiv:1402.3860v2, `V` has undistorted cyclic subgroups, with
consequences for nilpotent and Baumslag–Solitar subgroups). This lane checked that source
only as TeX statements.

The stronger (V0+) of part 3, "only finitely many hyperbolic periodic orbits", is not
proved here.
